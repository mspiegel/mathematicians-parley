"""Turn a readable proof into a Metamath proof.

`ELABORATION.md` lists what the expansion language has to have, read off five
proofs worked out by hand and then off three more this program elaborated.
`obtain`, `contradiction`, `fix` and `induction` open scopes; `substitute`,
`calculation`, `join` and `exhibit` are steps; a definition may be unfolded,
read the other way, or used to conclude an existence claim; a name may be
introduced by a `define`; and a theorem may be cited whether set.mm supplies
it or this corpus proves it.

Two things shape the code. A step is elaborated in deduction form, so every
line is an implication whose antecedent is the scope it sits in, and a step's
expansion is a function of the step and of that scope rather than of the step
alone. And the readable layer writes which side condition a step needs but
never how to prove it, so what the text leaves out — that a product of
integers is an integer, that an integer is a complex number, that a
set-builder over a set is a set — is settled from the lemmas
`rules.MEMBERSHIP` names.

What is not expanded is stated at the head of the file it writes: a closure
method, or an item the database gives no target for. Each becomes an axiom
claiming exactly what the readable line claims, under the `requires` lines
that line carries and the lines it cites. Both, or the axiom says more than
the method does and the proof above it goes unused.

A theorem is named in full, by its proof file's path and its own name:
`parley/elaborate.py proof/sqrt2-irrational/odd-square <set.mm>`.

Usage:  parley/elaborate.py <theorem> <set.mm>
"""
import hashlib
import re
import sys
from pathlib import Path

import kernel
import rules
import targets
from build import DEFINITIONS, path_of
from calculators import Calculators
from compress import compressed, shapes
from compress import labels as compress_labels
from formula import Grammar
from library import Signature
from library import read as read_library
from match import binding_context, instantiation, match
from match import names as names_in
from parse import (
    STDLIB,
    Declined,
    Problem,
    corpus,
    declined,
    fmt,
    proved,
    qualified,
)
from parse import index as full_names
from provenance import REQUIRES, ProofRules
from reading import CLASS_NAMES, Reading, hypothesis_body, render
from scopes import Fact, Scopes
from sorts import sorts_in_scope
from spell import Builder, Proof, seq
from tables import TableReading

# Past the last line any proof has, for reading every define that is left.
_ENDLESS = float('inf')
# What the library proves below the readable layer, read alongside set.mm so
# a `target` may name its labels.
GEOMETRY = f'{STDLIB}/geometry'
# Variables for a name the proof does not spell: what a `define` renames
# its body's binders to, and what an `obtain` introduces. A name the text
# does spell keeps its own letter, so this holds what a reader is least
# likely to write, and holds enough of them that a proof binding several
# names of its own does not run the list out.
SPARE_VARS = ['vm', 'vk', 'vj', 'vi', 'vp', 'vq', 'vr', 'vs', 'vt', 'vu',
              'vo', 'vl', 'vg', 'vh', 'vf', 'vw', 'vv']
# Stands where a join would name the constructor, for a biconditional a
# lemma states the other way round from the way a step reaches it. It is no
# label, so a statement built from it would not spell, which is what stops a
# second antecedent being folded past one read this way.
TURNED = 'the other way round'


def label_of(name, taken=(), path='', line=0, ours=()):
    """What this elaborator calls a theorem it has written out.

    set.mm proves some of what this corpus proves and has its own names for
    them, so the label is moved off any that is already in use: `sqrt2irr`
    is taken. The corpus's own theorems can share a stem as well —
    `powerset-split` and `powerset-split-disjoint` are both `powerset`, and
    two proof files may each hold a theorem of one name — and the files
    that hold them are read together, so `ours`, the full names of every
    theorem the corpus proves, are given labels one at a time in order of
    full name, each moved off what set.mm and the ones before it hold. The
    stem is the theorem's own name, without its file's path.
    Which label a theorem lands on then depends only on set.mm and the
    corpus, so a theorem that cites another agrees with the file that wrote
    it.

    Where it runs out of names the theorem is the thing to rename, so its
    own place is what the defect carries. This is the one defect outside
    `Elaborator`, which is why it is passed rather than known.
    """
    given = {}
    for one in sorted({*ours, name}):
        stem = one.rsplit('/', 1)[-1].replace('-', '')[:8]
        held = set(given.values())
        free = [s for s in (stem, *(f'{stem[:7]}{d}' for d in range(1, 10)))
                if s not in taken and s not in held]
        if not free:
            raise Problem(path, line, f'no free label near {stem!r}')
        given[one] = free[0]
    return given[name]


def proved_here(items):
    """The full names of the theorems this corpus proves.

    `label_of` needs them.
    """
    return {name for name, item in items.items() if proved(item)}


class Elaborator(Reading, Scopes, TableReading, Calculators, ProofRules,
                 Builder):
    def __init__(self, thm, grammar, items, sigs, records):
        super().__init__(sigs)
        # Every definition and theorem by its full name, the proved theorems
        # of the corpus among them, as `parse.index` gives them.
        self.thm, self.g, self.items = thm, grammar, items
        self.terms = targets.terms(records)
        # A name the proof introduces becomes a variable of the kernel, and it
        # must not be one a notation's own target binds: `S(_)` sums over `k`,
        # so a proof that fixes `k` cannot be given `k`.
        self.taken = {t for entries in self.terms.values()
                      for e in entries if e for t in e.split()}
        self.spare = [v for v in SPARE_VARS if v not in self.taken]
        self.commutes = targets.commuting(records)
        self.cited = []          # corpus theorems this proof leans on
        self.joined = None
        self.enclosing = None    # the block a step sits directly inside
        self.shapes = {}         # target pattern -> the tree it reads as
        # Where the elaborator has got to, for whatever it reads there. The
        # theorem's own line until a step sets it, so a hypothesis or a
        # conclusion that will not parse points at the theorem.
        self.at = thm.line
        self.names = {}          # readable name -> kernel term
        self.fixed = {}          # the same, as the theorem's `let` lines left
                                 # it, for the names a notation holds fixed
        self.sets = {}           # readable name -> the set it was let into
        self.axioms = []         # (label, statement) for each algebra step
        self.arities = {}        # cited corpus label -> how much it takes
        self.reserved = set()    # setvars the conclusion quantifies over
        self.supplying = set()   # `requires` terms being discharged now
        self.rests_on = {}       # by page item, what its proof was built on
        self.bridges = None      # (from system, to system) -> one lemma
        self.citing = frozenset()    # the lines what is being proved cites
        self.resting = None      # what the proof being built may rest on
        self.combined = {}           # by step line, what its method combined
        self.sorts = frozenset()     # labels of set, point and function lines
        self.defines = frozenset()   # labels of `define` lines
        self.written = {}        # side conditions the step being proved wrote
        self.saying = set()      # terms `said_otherwise` is working on now
        self.rewriting = set()   # terms `rewritten` is working on now
        self.numbering = set()   # memberships `numeral_within` works out now
        self.numbers = {}        # (membership, scope) -> what it came to
        self.bound_as = {}       # binder name -> the setvar it stands for
        self.assumed = {}        # statement -> how it is pushed, stated once
        self.unread = 0          # how far down the `define` lines we have read
        self.last = None
        # `Builder` gives the name-to-label direction; this is the other one.
        self.fname = {v: k for k, v in self.flabel.items()}
        # Which pattern of a record matched is read from the node's literal,
        # so a record's patterns are listed by theirs, in the order the
        # `pattern` and `target` fields both use. A folded pattern carries the
        # literal of the one it folds into, which is what makes the first
        # match the right entry.
        self.literals, self.binders = {}, {}
        for n in grammar.notations:
            self.literals.setdefault(n.name, []).append(n.literal)
            # A binder may introduce more than one name: `there are p ∈ ℤ and
            # q ∈ ℤ with ...` binds two.
            said = re.match(r'holes?\s+([\d\s and]+?)\s+over', n.binds or '')
            if said:
                self.binders[n.name] = {int(d) - 1
                                        for d in re.findall(r'\d+',
                                                            said.group(1))}

    def defect(self, line, message):
        """Something a person has to fix, and where in the proof it is.

        Every defect raised below is a place in the text this elaborator is
        reading: the line is the step's or the define's, and the file is
        the one the theorem was read from. So no raise site says which file
        it is in, and none of them can be wrong about it.

        A defect that names a line and no file names half a place, and
        `parley/test_elaborate.py` asserts the whole of one.
        """
        return Problem(self.thm.path, line, message)

    def no(self, shape, *terms):
        """This route does not apply, and why, in the terms as they stand.

        The words are put together only if something reads them, which
        almost nothing does: the route that asked goes on to the next. That
        is what a decline is for, and writing a term out the way a Metamath
        file writes it is not cheap — this is given back 1.2 million times
        in elaborating the geometric series alone.
        """
        return Declined(shape, terms, self.render)

    # --- facts the text never writes ----------------------------------------

    def settle(self, wanted, scope, facts, depth=3, step=None, lines=None):
        """A proof of something a step needs and the text does not write.

        `depth` bounds how many declared lemmas a chain applies one on top
        of another, and three is the deepest chain in the corpus: step 2.1
        of the geometric series needs `A^0 ∈ ℂ`, which is `recn` from
        `A^0 ∈ ℝ`, which is `reexpcl` asking `0 ∈ ℕ₀`, which is `0nn0`.
        Three other theorems need three as well. That a term is a set is not
        searched for and spends none of it (`made_a_set`), and neither does
        splitting a conjunction: there is one way to prove both halves, and
        the parts are smaller.

        What is offered is only what the proof being built may rest on
        (`resting_on`), so a route through a line the step does not name
        is not there to be found, whatever order the lemmas are tried in.

        A cited lemma asks side conditions of its own — that an index is in
        the upper integers, that a summand is complex — and those are not
        `requires` lines, because to a reader they are not steps. They are
        settled from the lemmas `rules.MEMBERSHIP` names, by matching what
        each concludes against what is wanted, and failing that from what is
        wanted read through an equation the step cites (`rewritten`).

        A step is passed only where one is there to have cited a witness,
        which is what lets an existential be proved at all. Side conditions
        pass none, so they stay what they are: settled from declared
        lemmas, never by finding a fact that happens to fit.
        """
        if self.resting is not None:
            facts = {k: v for k, v in facts.items()
                     if getattr(v, 'origin', frozenset()) <= self.resting}
        rpn = wanted.rpn(self.flabel)
        if rpn in facts:
            return facts[rpn]
        # A number's membership of a number system is worked out from the
        # numeral, not searched for, and spends none of the depth: a digit
        # is set.mm's label for it, `9cn` or `9nn0`, and 10 or 10^0 − 1 is
        # built from its digits (`numeral_within`). Spending depth on it
        # left 10^k ∈ ℤ, deep inside a sum's term, one level short of 10.
        if wanted.label == 'wcel' and len(wanted.children) == 2 \
                and wanted.children[1].label in rules.SYSTEMS \
                and not set(wanted.children[0].rpn(self.flabel).split()) \
                - rules.NUMERIC:
            # Inside the search that works out one number, the numbers it
            # is built from are looked up and not searched for again: each
            # starting its own search made 21,000 of them for one theorem.
            number = (self.digit_within(wanted, scope, facts)
                      if self.numbering
                      else self.numeral_within(wanted, scope, facts))
            if not declined(number):
                return number
        # Whether a term is a set is read off its structure, not searched
        # for: the constructor at its head says which lemma, and what the
        # lemma asks is its parts' sethood, which comes back here.
        if (wanted.label == 'wcel' and len(wanted.children) == 2
                and wanted.children[1].rpn(self.flabel) == 'cvv'):
            made = self.made_a_set(wanted, scope, facts)
            if not declined(made):
                return made
        # A membership a requires line wrote in another number system is the
        # one to carry, before the lemmas below are tried in their order:
        # `nncn` stands before `recn`, and would take `A ∈ ℂ` from the
        # hypothesis `A ∈ ℕ` rather than from the line saying `A ∈ ℝ`.
        if wanted.label == 'wcel' and len(wanted.children) == 2:
            found = self.bridged(wanted.children[0].rpn(self.flabel),
                                 wanted.children[1].rpn(self.flabel),
                                 scope, facts)
            if found is not None:
                return found
        # A sum, difference, product, power or negation is in a number
        # system because its parts are, and that is read off the operation,
        # spending none of the depth (`closed_under`).
        if wanted.label == 'wcel' and len(wanted.children) == 2 \
                and wanted.children[1].label in rules.SYSTEMS:
            made = self.closed_under(wanted, scope, facts, depth)
            if not declined(made):
                return made
        if wanted.label in rules.BOUND:
            # A `define` and a `fix` may write the same letter, and one of
            # them is renamed so that they do not collide. The line is then
            # the line wanted spelt with another binder, which is the same
            # line: `ralrnmpt` asks over the name its map binds where the
            # proof wrote its own.
            for said, proof in facts.items():
                spelt = self.respelt(proof, said, rpn, scope)
                if spelt is not None:
                    return spelt
        if depth > 0:
            joined = self.conjoined(
                wanted, scope,
                lambda one: self.settle(one, scope, facts, depth, step,
                                        lines))
            if joined is not None:
                return joined
            if wanted.label == 'wrex' and step is not None:
                return self.witnessed(step, wanted, scope, facts,
                                      lines or {})
            if wanted.label == 'wral':
                # A side condition may be asked of every member at once:
                # `ralrnmpt` wants each of its map's values to be a set. The
                # name is fixed, the condition settled of it, and
                # `ralrimiva` gives it back, which is `as_generalised` over
                # a declared lemma rather than over a cited one.
                #
                # Going under the binder spends no depth, as splitting a
                # conjunction spends none. It is one claim said of one
                # member, not a step of the chain the bound is there to cut
                # off, and spending it stopped `f1mpt` halfway.
                body, variable, over = wanted.children
                member = self.seq(f'{variable.rpn(self.flabel)} cv',
                             over.rpn(self.flabel), 'wcel')
                frame = len(self.frames)
                inner, lifted = self.widen(scope, facts, member)
                made = self.settle(body, inner, lifted, depth)
                del self.frames[frame:]
                if declined(made):
                    return made
                return self.seq(scope, body.rpn(self.flabel),
                           variable.rpn(self.flabel),
                           over.rpn(self.flabel), made, 'ralrimiva')
            # Every lemma is tried as it is written before any is read
            # backwards, so that a biconditional turned round never stands
            # in for one that says what is wanted outright.
            for backwards in (False, True):
                for label in rules.MEMBERSHIP:
                    sig = self.sigs.get(label)
                    if sig is None:
                        continue
                    found = self.fits(label, sig, wanted, scope, facts,
                                      depth, backwards)
                    if found is not None:
                        return found
            found = self.said_otherwise(wanted, scope, facts, depth)
            if found is not None:
                return found
            found = self.rewritten(wanted, scope, facts, depth)
            if not declined(found):
                return found
        return self.no('cannot settle {}', rpn)

    def rewritten(self, wanted, scope, facts, depth):
        """What is wanted, with a term in it put as an equation in hand says.

        `hashgt0elex` asks that a set's size be positive, and the subsets
        proof says what the size is: |X| = k + 1, the line the step cites.
        Nothing declared says a size is positive, and something does say
        k + 1 is, once the size is read as the line says. So the term is
        replaced by what the equation equates it to, what is left is
        settled, and the congruence carries it back.

        The equations are the ones in `facts`, which during a step is what
        the step names and the sorts (`resting_on`), and the sorts are
        never equations. So this rewrites only by a line the step cites,
        and a line merely in scope rewrites nothing.

        Only a term built from others is replaced, never a name or a
        constant. Putting a name's value in its place is what a
        `substitute` line writes, so a reader sees it done; a size or a sum
        read as a line equates it is the step's own business. No proof in
        the corpus needs more, and none changes when names are allowed too.
        Each rewrite spends a level, and a term already being rewritten is
        not rewritten again, so the rewrites stop.
        """
        want = wanted.rpn(self.flabel)
        if want in self.rewriting:
            return self.no('{} is already being rewritten', want)
        self.rewriting.add(want)
        try:
            return self.rewrite_by_facts(wanted, want, scope, facts, depth)
        finally:
            self.rewriting.discard(want)

    def rewrite_by_facts(self, wanted, want, scope, facts, depth):
        """One pass over the equations in hand, for `rewritten`."""
        for said in list(facts):
            equation = self.to_term(said)
            if equation.label != 'wceq' or len(equation.children) != 2:
                continue
            left, right = equation.children
            for old, new in ((left, right), (right, left)):
                if old.variable is not None or not old.children \
                        or old.label == 'cv':
                    continue
                was, now = old.rpn(self.flabel), new.rpn(self.flabel)
                # A numeral is a constant however set.mm spells it — 10 is
                # the decimal `; 1 0` — and so is a sum of them. A cited
                # 9 + 1 = 10 rewrote each into the other at every level of
                # every search that failed, and a build ran for minutes.
                if not set(was.split()) - rules.NUMERIC:
                    continue
                put = self.replaced(wanted, was, new)
                if put.rpn(self.flabel) == want:
                    continue
                under = self.settle(put, scope, facts, depth - 1)
                if declined(under):
                    continue

                def stands(one, other, where, held, was=was, now=now,
                           said=said, flip=old is left):
                    if (one.rpn(self.flabel) != now
                            or other.rpn(self.flabel) != was):
                        return None
                    if said not in held:
                        return self.no('{} is not in hand here', said)
                    # The line says `was = now` or `now = was`, and what
                    # carries the settled term back is `now = was`.
                    return (self.seq(where, was, now, held[said], 'eqcomd')
                            if flip else held[said])

                alike = self.congruence(put, wanted, scope, facts, None,
                                        stands)
                if declined(alike):
                    continue
                return self.seq(scope, put.rpn(self.flabel), want, under,
                                alike, 'mpbid')
        return self.no('no equation in hand rewrites {}', want)

    def replaced(self, term, was, new):
        """`term` with every occurrence of the term spelt `was` put as `new`."""
        if term.rpn(self.flabel) == was:
            return new
        if term.variable is not None or not term.children:
            return term
        return kernel.Term(term.label,
                           tuple(self.replaced(c, was, new)
                                 for c in term.children))

    def said_otherwise(self, wanted, scope, facts, depth):
        """What is wanted, held by the scope under another name for a term.

        `divalg` bounds the remainder by the absolute value of the divisor
        and the readable line bounds it by the divisor, which are the same
        bound because the divisor is a natural number. So a declared
        equation is asked whether the fact in hand is the fact wanted said
        differently, and the congruence carries it across.

        The equation is declared, like everything else this may lean on,
        and it is asked only of terms the wanted actually contains — a
        lemma that rewrote anywhere would reach claims by means the text
        never names.

        A term already being asked about is not asked about again. What
        this reaches through eventually asks `settle` afresh, which starts
        its depth over, so the two of them together have nothing that must
        decrease and would go round until the stack gave out. It used to go
        round until the stack gave out and then catch that, which is a
        stack overflow read as a route declining; this is the same cut made
        where it can be seen. `supplying` guards `requires` the same way.
        """
        want = wanted.rpn(self.flabel)
        if want in self.saying:
            return None
        self.saying.add(want)
        try:
            return self.otherwise(wanted, want, scope, facts, depth)
        finally:
            self.saying.discard(want)

    def otherwise(self, wanted, want, scope, facts, depth):
        """One pass over the declared equations, for `said_otherwise`."""
        for label in rules.MEMBERSHIP:
            sig = self.sigs.get(label)
            if sig is None or sig.essentials:
                continue
            says = self.syntax.statement(sig)
            names, reads = says.names(), says
            while reads.label == 'wi':
                reads = reads.children[1]
            if reads.label != 'wceq' or len(reads.children) != 2:
                continue

            def stands(one, other, where, _held, reads=reads, names=names,
                       label=label):
                """The one place the fact and the wanted differ, if the
                equation is what stands between them.
                """
                bound = kernel.match(reads.children[0], one, {}, names)
                if bound is None or reads.children[0].names() - set(bound):
                    return None
                if reads.children[1].substitute(bound).rpn(self.flabel) \
                        != other.rpn(self.flabel):
                    return None
                return self.apply_lemma(
                    label, self.to_term(self.seq(one.rpn(self.flabel),
                                            other.rpn(self.flabel), 'wceq')),
                    where, facts, None, crossing=False)

            for said, proof in list(facts.items()):
                if said == want:
                    continue
                alike = self.congruence(self.to_term(said), wanted,
                                        scope, facts, None, stands)
                if declined(alike):
                    continue
                if alike is not None:
                    return self.seq(scope, said, want, proof, alike, 'mpbid')
        return None

    def fits(self, label, sig, wanted, scope, facts, depth, backwards):
        """Whether one lemma settles what is wanted, and how.

        A biconditional says two things, so it can be read either way:
        `elnnuz` puts a natural number in the upper integers from its left
        side, and `eluz2` puts something there from an inequality, which is
        its right. Which way is the caller's, since reading one backwards
        is a last resort.

        A lemma may ask something and only then say its two things: `rexss`
        wants one set inside another before it will say that quantifying
        over the smaller is quantifying over the larger with the smaller in
        the body. So the asking is peeled off first and what is left is read
        the same way a bare biconditional is.
        """
        whole = self.syntax.statement(sig)
        asks, joins, reads = [], [], whole
        while reads.label == 'wi':
            asks.append(reads.children[0])
            joins.append('wi')
            reads = reads.children[1]
        if whole.label == 'wb':
            side = 0 if backwards else 1
            readings = [([whole.children[1 - side]], ['wb'],
                         whole.children[side])]
            # and the biconditional itself, which is what `crossed` asks
            # for when `rextru` is the bridge between two existentials
            if not backwards:
                readings.append(((), (), whole))
        elif reads.label == 'wb':
            # Asked something and then said two things. Either side may be
            # what is wanted, and so may the whole biconditional, which is
            # what a caller wanting the equivalence itself asks for.
            side = 0 if backwards else 1
            readings = [([*asks, reads.children[1 - side]], [*joins, 'wb'],
                         reads.children[side])]
            if not backwards:
                readings.append(((), (), whole))
        else:
            # Nothing was said two ways, so the statement is read as it
            # stands and `fitting` peels it.
            readings = [] if backwards else [((), (), whole)]
        for antecedents, held, side in readings:
            found = self.fitting(label, sig, whole, list(antecedents),
                                 list(held), side, wanted, scope, facts,
                                 depth, backwards)
            if found is not None:
                return found
        return None

    def fitting(self, label, sig, whole, antecedents, joins, reads,
                wanted, scope, facts, depth, backwards=False):
        """One reading of a lemma, applied to what is wanted.

        A lemma may ask more than one thing before it says anything —
        `ltle` wants both sides real and then the strict relation — so its
        antecedents are peeled until what is left is what is wanted.

        `joins` says how each was joined to what followed it, which is what
        decides the lemma that discharges it. A reading that crosses a
        biconditional has one of each and they do not discharge alike.
        """
        variables = whole.names()
        binding = None
        while True:
            binding = kernel.match(reads, wanted, {}, variables)
            if binding is not None:
                break
            if reads.label != 'wi':
                return None
            antecedents.append(reads.children[0])
            joins.append('wi')
            reads = reads.children[1]

        # What the lemma concludes need not fix everything it asks, so an
        # antecedent still open is matched against something already known,
        # whole, and failing that a conjunct at a time, as `apply_lemma`
        # does: `ffvelcdm` asks `F : A --> B` and `C e. A` together, and
        # only the line saying what F maps between says what A is. What a
        # naming hypothesis decides comes first, as in `apply_lemma`:
        # `f1mpt` names its map, and a conjunct of what it asks matched
        # against a line otherwise binds the map's body to that line's.
        binding = self.opened(antecedents,
                              self.read_off(sig, binding, variables), facts,
                              variables)
        return self.fitted(label, sig, antecedents, joins, wanted, scope,
                           facts, depth, backwards, binding)

    def opened(self, antecedents, binding, facts, variables):
        """The binding with what the antecedents leave open filled in.

        A conjunct asking where to look for something rather than anything
        of it is left to `sethood`, which reads it so, and is not matched:
        `f1mpt` asks its map's values to lie in B, and matched alone against
        a fact putting one of them in some set, it bound B to that set and
        `add-element-bijection` failed.

        Every antecedent is matched whole before any is taken apart, so a
        conjunct matched alone never decides what a later antecedent says
        outright: `hashvnfin` asks `N e. NN0` beside `S e. V` and then
        `( # ` S ) = N`, and the first line in ℕ₀ is not the size.
        """
        binding = dict(binding)
        whole = []
        for slot in antecedents:
            if not slot.names() - set(binding):
                continue
            for held in facts:
                filled = kernel.match(slot, self.to_term(held), dict(binding),
                                      variables)
                if filled is not None:
                    binding = filled
                    break
            else:
                whole.append(slot)
        for slot in whole:
            for piece in self.conjuncts_of(slot):
                if not piece.names() - set(binding) \
                        or self.sethood(piece, binding):
                    continue
                for held in facts:
                    filled = kernel.match(piece, self.to_term(held),
                                          dict(binding), variables)
                    if filled is not None:
                        binding = filled
                        break
            # A class neither the claim nor a fact fixes is set.mm asking
            # where to look for the thing rather than asking anything of it,
            # which `apply_lemma` reads the same way: `pwexg` wants a class
            # holding the set whose power class is about to be one, and _V
            # holds every set. What is left is then settled.
            for open_slot in self.sethood(slot, binding):
                binding[open_slot] = kernel.Term('cvv')
        return binding

    def fitted(self, label, sig, antecedents, joins, wanted, scope, facts,
               depth, backwards, binding):
        """The lemma proved under one binding, or None where it is not."""
        variables = self.syntax.statement(sig).names()
        # A declared lemma may state a hypothesis in full rather than ask for
        # it, which is a spelling and not a difference in what it leans on:
        # `f1mpt` names its map that way. The two kinds it states are the two
        # `prove_essential` already knows — a naming and a relating — and
        # they are also what says which variables the claim did not fix.
        binding = self.instanced(sig, self.read_off(sig, binding, variables))
        essentials = [self.prove_essential(
            self.syntax.parse(e[1:], 'wff').substitute(binding),
            scope, facts) for e in sig.essentials]
        if any(declined(one) for one in essentials):
            return None
        proof = self.ap(label, self.spelt(binding), *essentials)
        if not antecedents:
            return self.seq(wanted.rpn(self.flabel), scope, proof, 'a1i')
        for i, slot in enumerate(antecedents):
            asks = slot.substitute(binding)
            rest = wanted.rpn(self.flabel)
            for later, join in reversed(list(zip(antecedents[i + 1:],
                                                 joins[i + 1:],
                                                 strict=True))):
                said = later.substitute(binding).rpn(self.flabel)
                # A biconditional read backwards states its sides the
                # other way round from the order they are taken in.
                rest = (self.seq(rest, said, 'wb')
                        if join == 'wb' and backwards
                        else self.seq(said, rest, join))
            under = self.settle(asks, scope, facts, depth - 1)
            if declined(under):
                return None
            first = proof.text.rsplit(None, 1)[-1] == label
            fold = rules.DISCHARGE[(joins[i], first)]
            if joins[i] == 'wb' and backwards:
                fold = 'sylibr' if first else 'mpbird'
            proof = self.seq(scope, asks.rpn(self.flabel), rest, under, proof,
                        fold)
        return proof

    # --- congruence ---------------------------------------------------------

    def shape(self, pattern):
        """A target read as a tree, so a rewrite can walk down it.

        A target need not be one constructor. `S(_)` is a sum over a range
        that holds the hole, so reaching the hole passes a `csu` and then a
        `co`, and each level wants its own congruence lemma.
        """
        if pattern in self.shapes:
            return self.shapes[pattern]
        stack = []
        for token in pattern.split():
            if token.startswith('_'):
                stack.append(('hole', int(token[1:]) - 1))
                continue
            count = len(self.sigs[token].floats)
            if not count:
                stack.append(('const', token))
                continue
            args = stack[len(stack) - count:]
            del stack[len(stack) - count:]
            # The operation is an operand of the lemma that rewrites under
            # it where it is a constant, as `cabs` is in |x|. Where it is a
            # hole it is an argument like any other: `application` targets
            # `_2 _1 cfv` and its function is `f`, which taken for a label
            # was its hole's index, and a zero `seq` leaves out.
            if token in rules.WRAPS and args[-1][0] == 'const':
                stack.append(('app', args[-1][1], token, args[:-1]))
            else:
                stack.append(('app', token, None, args))
        self.shapes[pattern] = stack[0]
        return stack[0]

    @staticmethod
    def holds(tree, wanted):
        if tree[0] == 'hole':
            return tree[1] == wanted
        if tree[0] == 'const':
            return False
        return any(Elaborator.holds(k, wanted) for k in tree[3])

    def spell(self, tree, holes):
        if tree[0] == 'hole':
            return holes[tree[1]]
        if tree[0] == 'const':
            return tree[1]
        _k, label, wrap, kids = tree
        parts = [self.spell(k, holes) for k in kids]
        return self.seq(*parts, label, wrap) if wrap else self.seq(*parts, label)

    def rewrite(self, node, old, new, scope, eqproof):
        """A proof that `node` equals `node` with `old` replaced by `new`.

        The path from the root of the claim to the occurrence decides the
        lemmas, one per step along it, and which hole the occurrence sits in
        decides which lemma. Nothing is searched for.
        """
        if self.term(node) == old:
            return new, eqproof
        # A binder's variable fills its slot as itself, and nothing rewrites
        # it: the claim is about what the binder ranges over, not about the
        # name it ranges under.
        bound = self.binders.get(node.notation, ())
        # The body speaks of what the binder introduces, as in `term`: the
        # lower limit of a sum is rewritten beside a summand that names k.
        saved = dict(self.names)
        for i in bound:
            said = node.children[i].text
            self.names[said] = f'{self.binder_var(said)} cv'
        try:
            holes = [self.binder_var(c.text) if i in bound else self.term(c)
                     for i, c in enumerate(node.children)]
            after, proofs = list(holes), {}
            for i, child in enumerate(node.children):
                if i in bound or old not in self.term(child):
                    continue
                made = self.rewrite(child, old, new, scope, eqproof)
                if declined(made):
                    return made
                after[i], proofs[i] = made
        finally:
            self.names = saved
        if not proofs:
            return Declined(f'nothing to rewrite in {self.term(node)}')
        return self.descend(self.shape(self.spelling(node)), holes, after,
                            proofs, scope)

    def descend(self, tree, before, after, proofs, scope):
        """Walk a target down to the holes that changed, a lemma a level."""
        if tree[0] == 'hole':
            return after[tree[1]], proofs[tree[1]]
        if tree[0] == 'const':
            return Declined('no hole changed under this target')
        _k, label, wrap, kids = tree
        was = [self.spell(k, before) for k in kids]
        now, deeper, slots = list(was), [], []
        for slot, kid in enumerate(kids):
            if not any(self.holds(kid, h) for h in proofs):
                continue
            made = self.descend(kid, before, after, proofs, scope)
            if declined(made):
                return made
            now[slot], under = made
            deeper.append(under)
            slots.append(slot)
        if not slots:
            return Declined('no hole changed under this target')
        # An operation or a relation is itself an operand of the lemma that
        # rewrites under it; a constructor that takes its arguments directly
        # is not. What changed comes first, old beside new, then the rest.
        built = self.seq(*now, label, wrap) if wrap else self.seq(*now, label)
        if (wrap or label) == 'csu' and 1 in slots:
            made = self.summand_changed(scope, was, now,
                                        dict(zip(slots, deeper, strict=True)))
            return made if declined(made) else (built, made)
        moved = [x for slot in slots for x in (was[slot], now[slot])]
        rest = [o for j, o in enumerate(was) if j not in slots]
        return built, self.seq(scope, *moved, *rest, label if wrap else '',
                          *deeper, rules.CONGRUENCE[(wrap or label,
                                                    tuple(slots))])

    def summand_changed(self, scope, was, now, proofs):
        """A sum rewritten where its summand changes, and its range maybe.

        The claim of an induction over a sum holds the variable in the
        summand as well as the limit: the binomial theorem's n is in both.
        `sumeq2sdv` rewrites the summand from an equation with no index in
        it, which set.mm lets it do only where the scope does not mention
        the index, as the induction's `x = y` does not. The range, where it
        changes too, is rewritten first by `sumeq1d`, and `eqtrd` joins the
        two. A scope that mentions the index declines here: set.mm's own
        lemma would be refused by the verifier.
        """
        limits, summand, index = was
        if index in scope.split():
            return Declined('the scope mentions the index the sum binds')
        rewritten = self.ap('sumeq2sdv', {'ph': scope, 'A': now[0],
                                          'B': summand, 'C': now[1],
                                          'k': index}, proofs[1])
        if 0 not in proofs:
            return rewritten
        moved = self.ap('sumeq1d', {'ph': scope, 'A': limits, 'B': now[0],
                                    'C': summand, 'k': index}, proofs[0])
        return self.ap('eqtrd', {'ph': scope,
                                 'A': self.seq(limits, summand, index, 'csu'),
                                 'B': self.seq(now[0], summand, index, 'csu'),
                                 'C': self.seq(now[0], now[1], index, 'csu')},
                       moved, rewritten)

    # --- definitions --------------------------------------------------------

    def unfolding(self, step, lemma, left, ex, var, over, scope, facts,
                  hint=None):
        """The biconditional a definition's lemma gives, in scope.

        A target need not take only the thing being defined, and need not ask
        only that it lie somewhere: `divides` unfolds `d || n` and wants both
        d and n in ZZ. Which of the lemma's variables the readable left side
        fills, and what the lemma then asks for, are read off its statement
        rather than assumed of it.

        Returns the proof and the right side it reached. `ex` is the wording
        the step wants; pass None to take whatever the lemma says.
        """
        sig = self.sigs[lemma]
        whole = self.syntax.statement(sig)
        asks, reads = [], whole
        while reads.label == 'wi':
            asks.append(reads.children[0])
            reads = reads.children[1]
        if reads.label != 'wb':
            return Declined(f'{lemma} states no biconditional')
        binding = kernel.match(reads.children[0], self.to_term(left), {},
                               whole.names())
        if binding is None:
            return self.no(f'{lemma} does not unfold {{}}', left)
        # A lemma's left side need not fix everything it mentions: `elrab`
        # names the body twice, once in the set-builder's variable and once
        # in the element's, and only the second is on the right. So what the
        # caller can say of the right side fixes the rest, and is taken only
        # where it fits.
        offered = hint if hint is not None else ex
        if offered is not None:
            filled = kernel.match(reads.children[1], self.to_term(offered),
                                  dict(binding), whole.names())
            if filled is not None:
                binding = filled
        # A slot neither side fixes is set.mm asking where to look for the
        # thing rather than asking anything of it: `elpwg` wants a class
        # holding what is about to be in the power class, and _V holds
        # everything that is a set.
        for slot in asks:
            for open_slot in slot.names() - set(binding):
                binding[open_slot] = kernel.Term('cvv')
        binding = self.instanced(sig, binding)
        # A definition that introduces a name says which variable it takes;
        # one that does not leaves the lemma's own, which the match fixed.
        binds = self.spelt(binding)
        if var is not None and sig.bound() is not None:
            binds[sig.bound()] = var
        # A lemma may state a condition in full rather than ask for it:
        # `elpw` wants what it is about to be a set before it will say what
        # belongs to its power class. Both are settled against the binding as
        # the match left it, before the wording below rebinds what it takes.
        applied = self.ap(lemma, binds, *[self.prove_essential(
            self.syntax.parse(e[1:], 'wff').substitute(binding), scope, facts)
            for e in sig.essentials])
        # The lemma unfolds to its own wording, which need not be the text's:
        # `divides` writes the product the other way round. What it gives is
        # built first, and the text's wording is reached from it.
        held = sig.bound()
        if held is not None and var is not None:
            binding[held] = kernel.Term(variable=self.sigs[var].statement[1])
        given = reads.children[1].substitute(binding).rpn(self.flabel)
        says = self.seq(left, given, 'wb')
        if not asks:
            proof = self.seq(says, scope, applied, 'a1i')
        else:
            holds = asks[0].substitute(binding).rpn(self.flabel)
            proof = self.required(step, holds, over, scope, facts)
            for slot in asks[1:]:
                extra = slot.substitute(binding).rpn(self.flabel)
                proof = self.seq(scope, holds, extra, proof,
                            self.required(step, extra, over, scope, facts),
                            'jca')
                holds = self.seq(holds, extra, 'wa')
            proof = self.seq(scope, holds, says, proof, applied, 'syl')
        if ex is None or given == ex:
            return proof, given
        # No bridge means the lemma unfolds to a wording this step cannot be
        # reached from, which is this route not applying rather than a defect:
        # a target may name several lemmas and the caller has others to try.
        across = self.bridging(self.to_term(given), self.to_term(ex), scope,
                               facts, step)
        if declined(across):
            return across
        return self.seq(scope, left, given, ex, proof, across, 'bitrd'), ex

    def substituted_slot(self, asked, binding):
        """A wff slot an essential fixes by saying it is a substitution.

        `elrab` holds a set-builder's body in `ph` and the same body about
        the element in `ps`, and asks `( x = A -> ( ph <-> ps ) )`. Nothing
        on its left side mentions `ps`, so where the claim has not filled it
        this hypothesis is the only thing that says what it is.

        Given only where every other part is settled: the body closed, the
        side being renamed a binder's `cv` over a setvar, and the slot
        still open. A slot standing for itself is open — the match binds a
        lemma's variable to its own name where nothing fixed it, and that
        is what a claim of one half of the right side leaves behind. A
        lemma asking anything else is left alone.
        """
        if asked.label != 'wi' or len(asked.children) != 2:
            return None
        same, iff = asked.children
        if same.label != 'wceq' or iff.label != 'wb':
            return None
        over, element = (one.substitute(binding) for one in same.children)
        body, slot = iff.children
        held = binding.get(slot.variable)
        if (slot.variable is None or over.label != 'cv'
                or over.children[0].variable is None
                or (held is not None and held.variable != slot.variable)
                or body.names() - set(binding)):
            return None
        # The body holds the variable as a binder writes it, `cv` over a
        # setvar; the element is a class. Stripping the `cv` is what lets
        # the one stand in for the other.
        name = over.children[0].variable
        said = self.as_class(body.substitute(binding), {name})
        return {slot.variable: said.substitute({name: element})}

    def witnessed(self, step, wanted, scope, facts, lines):
        """A restricted existential, from the line a step cites for it.

        The text never writes the witness as a witness: it writes a line
        that happens to name one. Bezout's step 2 puts `a` in a set-builder
        whose body is `there are m and n with t = a·m + b·n`, citing
        `a = a·1 + b·0`, and 1 and 0 are the witnesses because that line is
        the body with them in place.

        Taken from the lines the step cites and never searched for among
        the facts in scope. An existential is a step's own claim, so there
        is always a citation to read it off, and settling one by finding
        something that happened to fit would be proving a claim by a route
        the text never names.

        Built from the innermost quantifier out, which is the order the
        witnesses go in: `rspcev` wants the body at one witness and gives
        the existential over it, so the next one out is handed what the
        last one proved.
        """
        layers, rest = [], wanted
        while rest.label == 'wrex':
            body, var, over = rest.children
            layers.append((body, var.rpn(self.flabel),
                           over.rpn(self.flabel)))
            rest = body
        marks = {f'{v} cv' for _b, v, _o in layers}
        for ref in step.just.refs:
            cited = lines.get(ref)
            found = cited and self.witnesses_in(
                rest, self.to_term(cited.term), marks)
            if not found and cited and len(layers) == 1:
                found = self.member_named(cited.term, layers[0])
            if found:
                break
        else:
            raise self.defect(step.line, 'no cited line names a witness for '
                              f'{self.render(wanted.rpn(self.flabel))}')

        # The line that names the witnesses need not be all the claim says
        # of them: `thm:proof/sqrt2-irrational/lowest-terms` exhibits a p and
        # a q that one line says are a fraction in lowest terms, another says
        # is positive, and a third says nothing divides. Where it is all of it, its own
        # proof is taken, because that is fewer steps than settling it.
        proof = facts.get(cited.term, cited.proof)
        innermost = layers[-1][0]
        for _b, v, _o in layers:
            innermost = self.restated(innermost, f'{v} cv', found[f'{v} cv'])
        if innermost.rpn(self.flabel) == 'wtru':
            # A body that says nothing of its variable — S is not empty —
            # holds outright, by the one lemma that states truth.
            proof = self.seq('wtru', scope, 'tru', 'a1i')
        elif innermost.rpn(self.flabel) != cited.term:
            proof = self.settle(innermost, scope, facts, step=step,
                                lines=lines)
            if declined(proof):
                return proof
        for i in reversed(range(len(layers))):
            body, var, over = layers[i]
            mark, held = f'{var} cv', body
            # The quantifiers further out are still open here, and the ones
            # already closed have their witnesses in place.
            for _b, v, _o in layers[:i]:
                held = self.restated(held, f'{v} cv', found[f'{v} cv'])
            witness = found[mark]
            here = self.restated(held, mark, witness)
            ph = held.rpn(self.flabel)
            ps = here.rpn(self.flabel)
            # `rspcev` asks what `elrab` asks — the body before and after,
            # tied by the witness standing where the variable did — so the
            # same branch of `prove_essential` discharges it.
            if ph == ps:
                # The body does not mention the variable, so the witness
                # changes nothing in it: `biidd` says so outright.
                instance = self.seq(seq(mark, witness, 'wceq'), ph, 'biidd')
            else:
                instance = self.prove_essential(
                    self.to_term(self.seq(self.seq(mark, witness, 'wceq'),
                                          self.seq(ph, ps, 'wb'), 'wi')),
                    scope, facts)
                if declined(instance):
                    return instance
            member = self.seq(witness, over, 'wcel')
            proof = self.seq(scope, self.seq(member, ps, 'wa'), self.seq(ph, var, over,
                                                          'wrex'),
                        self.seq(scope, member, ps,
                            self.required(step, member, over, scope, facts),
                            proof, 'jca'),
                        ph, ps, var, witness, over, instance, 'rspcev', 'syl')
        return proof

    def member_named(self, said, layer):
        """The witness a line gives by putting something in the domain.

        A "there is s ∈ S" whose body says nothing of s — S is not empty —
        is not matched by what a line says of s, since it says nothing: its
        witness is whatever a cited line puts in S. `check.py` reads the
        same claim the same way, as stated by any fact putting something in
        S; the intermediate value theorem cites `a ∈ S`.
        """
        _body, var, over = layer
        for part in self.parts(said):
            node = self.to_term(part)
            if node.variable is None and node.label == 'wcel' \
                    and node.children[1].rpn(self.flabel) == over:
                return {f'{var} cv': node.children[0].rpn(self.flabel)}
        return None

    def restated(self, term, was, now):
        """`term` with every occurrence of the subterm `was` reading `now`.

        Both are given in reverse Polish, because a term is compared by what
        it spells: the kernel's terms are trees without an equality.
        """
        if term.rpn(self.flabel) == was:
            return self.to_term(now)
        if term.variable is not None:
            return term
        return kernel.Term(term.label,
                           tuple(self.restated(c, was, now)
                                 for c in term.children))

    def read_off(self, sig, binding, variables):
        """What a lemma's naming hypothesis says its own variables are.

        `ralrnmpt` names a map in a hypothesis and speaks of its range in
        the conclusion, so the claim fixes the map and nothing else. What
        the map binds, where that runs and what it builds are read back out
        of it, which is the same move `instanced` makes for a hypothesis
        relating two formulas: the lemma is saying what it means, not
        asking for something.

        What the map binds and builds may appear nowhere else: `elrnmpt1s`
        concludes only that something is in the range, and names the map's
        variable and body in its hypotheses alone. They are the lemma's
        variables all the same, so the naming is read over them too.
        """
        for text in sig.essentials:
            asked = self.syntax.parse(text[1:], 'wff')
            if asked.label != 'wceq' or len(asked.children) != 2:
                continue
            name = asked.children[0].variable
            if name is None or name not in binding:
                continue
            said = kernel.match(asked.children[1], binding[name],
                                dict(binding),
                                set(variables) | asked.names())
            if said is not None:
                binding = said
        return binding

    def instanced(self, sig, binding):
        """What a lemma asking `( x = A -> ( ph <-> ps ) )` means by `ps`.

        Such a lemma states how its own two sides are related rather than
        asking: `ps` is `ph` with the variable reading the term. `elrab`
        reads a set-builder's body at the element, `rspcev` reads a body at
        a witness, and in both the relation is the lemma's own.

        So it is worked out and not taken from the step. A citation offering
        something else is offering evidence for `ps` rather than `ps`: the
        Bezout proof puts `a` in a set-builder whose body is an existential
        over m and n, citing `a = a·1 + b·0`, and reading that as `ps` asks
        for a biconditional between an existential and one of its instances,
        which is false.

        A hypothesis relating two terms says the same thing of them as one
        relating two formulas says of those: `fsum1` asks `( k = M -> A =
        B )`, and B is the summand read at M.
        """
        out = dict(binding)
        for text in sig.essentials:
            asked = self.syntax.parse(text[1:], 'wff')
            if asked.label != 'wi':
                continue
            at, says = asked.children
            if (at.label != 'wceq' or says.label not in ('wb', 'wceq')
                    or at.children[0].label != 'cv'):
                continue
            name = says.children[1].variable
            if name is None:
                continue
            # Read at a class nothing has fixed yet, the body would be read
            # at the lemma's own variable. `elrnmpt1s` learns what it reads
            # its map at from a line the step cites, which comes later, and
            # the claim has already said what the result is. A set variable
            # left open is different: `f1mpt` reads its map at one, and it
            # stands in the proof as a name of its own.
            kinds = dict((v, t) for t, v in sig.floats)
            if any(kinds.get(v) == 'class' for v in at.names() - set(out)):
                continue
            was, now = (c.substitute(out).rpn(self.flabel)
                        for c in at.children)
            out[name] = self.restated(says.children[0].substitute(out),
                                      was, now)
        return out

    def exchanged(self, given, want):
        """Whether these are one term with a commuting pair exchanged.

        `commutes` in `db/notation.records` is what says which operands may be,
        and which theorem proves it is not asked here: the exchange is an
        equation, and an equation is settled like anything else.
        """
        for label, places, fixed in self.commutes:
            if given.label != label or want.label != label:
                continue
            if len(given.children) != len(want.children) != len(fixed) + 2:
                continue
            spelt = [c.rpn(self.flabel) for c in given.children]
            other = [c.rpn(self.flabel) for c in want.children]
            if any(spelt[i] != token or other[i] != token
                   for i, token in fixed.items()):
                continue
            one, two = places
            if spelt[one] == other[two] and spelt[two] == other[one]:
                return True
        return False

    def bridging(self, given, want, scope, facts, step):
        """A proof that two terms differing by an exchange agree.

        set.mm writes `( k x. 2 )` where the corpus writes 2k, and those are
        the same number but not the same formula.
        """
        def swapped(one, other, where, held):
            if not self.exchanged(one, other):
                return None
            return self.settle(self.to_term(
                self.seq(one.rpn(self.flabel), other.rpn(self.flabel), 'wceq')),
                where, held)
        renamed = self.renaming(given, want)
        if renamed is not None:
            return self.seq(self.seq(given.rpn(self.flabel), want.rpn(self.flabel),
                           'wb'), scope, renamed, 'a1i')
        return self.congruence(given, want, scope, facts, step, swapped)

    def renaming(self, given, want):
        """The two as one claim, spelt with different bound variables.

        A `define` renames what its body binds, because the proof may go on
        to fix a name spelt the same way: Bezout's S binds a j where the
        step that reads it writes an n. `cbvrexvw` is set.mm saying those
        are one claim, and `cbvrexv` says it too by way of ax-13, which
        set.mm discourages.

        Closed, and lifted by closed lemmas. `rexbidva` would carry the
        scope under the binder and forbids the binder in what it carries,
        and the scope here names the very set-builder whose body binds it.
        None of this wants a scope: the two are one claim wherever they
        stand.
        """
        if given.rpn(self.flabel) == want.rpn(self.flabel):
            return None                        # nothing is spelt differently
        if (given.label != want.label
                or len(given.children) != len(want.children)):
            return None
        under = rules.BOUND.get(given.label)
        if under is not None:
            same, cross, over = *under, None
            if len(given.children) == 3:
                body, variable, over = given.children
                other, renamed, runs = want.children
                if over.rpn(self.flabel) != runs.rpn(self.flabel):
                    return None
            else:
                (body, variable), (other, renamed) = (given.children,
                                                      want.children)
            binds = {'ph': body.rpn(self.flabel),
                     'ps': other.rpn(self.flabel),
                     'x': variable.rpn(self.flabel)}
            if over is not None:
                binds['A'] = over.rpn(self.flabel)

            def bound(said, at=binds['x'], runs=over):
                """One binder put back around a body."""
                return (self.seq(said, at, runs.rpn(self.flabel), given.label)
                        if runs is not None else self.seq(said, at, given.label))

            if variable.variable == renamed.variable:
                inner = self.renaming(body, other)
                return None if inner is None else self.ap(same, binds, inner)
            # The cross lemma changes one binder and wants a hypothesis
            # relating the two bodies at x = y, which a body still spelt
            # two ways inside is not. So the bodies are made to agree
            # first, over this binder as it stands, and only then is it
            # changed.
            here = self.restated(other, f'{renamed.rpn(self.flabel)} cv',
                                 f'{variable.rpn(self.flabel)} cv')
            middle = dict(binds, ph=here.rpn(self.flabel))
            at = self.seq(self.seq(f'{variable.rpn(self.flabel)} cv',
                         f'{renamed.rpn(self.flabel)} cv', 'wceq'),
                     self.seq(middle['ph'], binds['ps'], 'wb'), 'wi')
            said = self.prove_essential(self.to_term(at), '', {})
            if declined(said):
                return None
            changed = self.ap(cross, dict(
                middle, y=renamed.rpn(self.flabel)), said)
            if middle['ph'] == binds['ph']:
                return changed
            inner = self.renaming(body, here)
            if inner is None:
                return None
            agreed = self.ap(same, dict(binds, ps=middle['ph']), inner)
            return self.ap('bitri', {'ph': bound(binds['ph']),
                                     'ps': bound(middle['ph']),
                                     'ch': want.rpn(self.flabel)},
                           agreed, changed)
        spelt = [c.rpn(self.flabel) for c in given.children]
        other = [c.rpn(self.flabel) for c in want.children]
        # Both halves of an implication may be spelt differently at once —
        # an induction's step claims P(k) -> P(k+1) in the part's own name
        # where the lemma wants the pattern's. The lifters each change one
        # side and hold the other, so the sides are changed one at a time
        # and the halfway claim is what joins the two.
        here, start, proof = list(spelt), self.seq(*spelt, given.label), None
        for slot in (i for i in range(len(spelt)) if spelt[i] != other[i]):
            label = rules.RENAMED.get((given.label, (slot,)))
            if label is None:
                return None
            inner = self.renaming(given.children[slot], want.children[slot])
            if inner is None:
                return None
            rest = here[1] if slot == 0 else here[0]
            step = self.ap(label, {'ph': here[slot], 'ps': other[slot],
                                   'ch': rest}, inner)
            was = self.seq(*here, given.label)
            here[slot] = other[slot]
            if proof is None:
                proof = step
                continue
            proof = self.ap('bitri', {'ph': start, 'ps': was,
                                      'ch': self.seq(*here, given.label)},
                            proof, step)
        return proof

    @staticmethod
    def subject_of(node):
        while node.children:
            node = node.children[0]
        return node

    # --- the proof ----------------------------------------------------------

    def run(self):
        nodes = self.hypotheses()
        # A notation may hold a name no hole of it fills, and that name is
        # bound where the definition introducing it stands rather than where
        # the notation is written: `def:stdlib/sums/G` says `let a ∈ ℝ`, and
        # every `G(n)` below is about that `a`. The theorem's `let` lines are
        # that place, and they are read before its conclusion and before any
        # step, so what is taken here is what the text fixed. Nothing writes it again,
        # which is what stops a block binding the same letter from reaching
        # it.
        self.fixed = dict(self.names)
        # A sort is stated once, like a declared type, and a step may rest
        # on it without naming it (`READERS.md`). A define is never emitted,
        # so naming one is never a use of it.
        lets = [*self.thm.hypotheses,
                *(o for s in self.thm.steps for o in s.openers)]
        self.sorts = frozenset(
            o[2] for o in lets if o[0] == 'let' and o[2]
            and (' be a set' in o[1] or ' be a point' in o[1]
                 or '→' in o[1]))
        self.defines = frozenset(d[2] for d in self.thm.defines)
        # What stands above the first step is the theorem's own, and the
        # hypotheses and the conclusion below may lean on it.
        self.defined(self.thm.steps[0].line if self.thm.steps else _ENDLESS)
        terms = [self.term(n) for n in nodes]
        # A theorem may assume nothing, and every step here is still an
        # implication out of the scope it sits in. So the scope is truth,
        # which is discharged once at the end.
        scope = terms[0] if terms else 'wtru'
        facts = {scope: self.seq(scope, 'id')}
        for extra in terms[1:]:
            wider = self.seq(scope, extra, 'wa')
            facts = {k: self.seq(wider, scope, k, self.seq(scope, extra, 'simpl'), v,
                            'syl')
                     for k, v in facts.items()}
            facts[extra] = self.seq(scope, extra, 'simpr')
            scope = wider
        # Each hypothesis stands for itself, and is sealed before it is taken
        # apart so that what it says in pieces is still what it says.
        for h, t in zip(self.thm.hypotheses, terms, strict=True):
            if h[2] and t in facts:
                facts[t] = self.seal(facts[t], h[2])
        # A hypothesis may say several things at once — `A, B, C form a
        # triangle` says three — and each of them is a fact the proof may
        # lean on without a step to take it apart.
        for extra in terms:
            if extra in facts:
                self.unpack(extra, facts[extra], scope, facts)
        self.sorts = self.sorts | self.sethoods(nodes, terms, scope, facts)

        lines = {h[2]: Fact(t, facts[t])
                 for h, t in zip(self.thm.hypotheses, terms, strict=True)}
        # What the conclusion quantifies over is spoken for before anything
        # else takes a variable. The primes proof concludes that there is a
        # prime p above n and obtains a p along the way, and those are two
        # different numbers however the text spells them.
        goal = self.claim_of(self.thm.conclusion)
        self.reserved = {t for t in goal.split()
                         if t in self.sigs
                         and self.sigs[t].statement[0] == 'setvar'}
        self.frames = [(scope, None, facts)]
        # A `requires` line names the lines it rests on, and what supplies it
        # is reached from places the step's own lines are not passed to.
        self.lines = lines
        closers, blocks = [], []
        for step in self.thm.steps:
            # A block's children are the steps numbered below it, so the
            # block closes at the first step that is not one of them.
            while blocks and len(step.number) <= len(blocks[-1].owner.number):
                done = blocks.pop()
                scope, facts, closers = self.close_block(done, facts, lines,
                                                         closers, scope)
                self.hand_up(done, blocks)
            # Any define standing above this step, now that the block it
            # sits in is open and the names it leans on are in hand.
            self.defined(step.line)
            # A step in a case sits under the case's assumption, a block as
            # much as a plain step: the intermediate value proof's first
            # case opens with a contradiction whose second step substitutes
            # into that assumption.
            # Only where the part is new. Within a part the scope is what the
            # steps before this one left it: an obtain opens one of its own,
            # and resetting to the case's lost what it obtained.
            if blocks and blocks[-1].assumed and step.part is not None \
                    and blocks[-1].entered != step.part:
                closers = self.end_case(blocks[-1], closers)
                scope, facts = self.enter_case(blocks[-1], step.part, lines)
                blocks[-1].case_opened_at = len(closers)
            if step.openers or step.parts:
                block = self.open_block(step, scope, facts, lines)
                block.opened_at = len(closers)
                blocks.append(block)
                scope, facts = block.scope, block.facts
                continue
            self.enclosing = blocks[-1] if blocks else None
            scope, facts, closers = self.step(step, scope, facts, lines,
                                              closers)
            if step.part is not None and blocks:
                held = lines[self.last]
                blocks[-1].parts[step.part] = (held.term, held.proof, scope)
        while blocks:
            done = blocks.pop()
            scope, facts, closers = self.close_block(done, facts, lines,
                                                     closers, scope)
            self.hand_up(done, blocks)

        proof = lines[self.last].proof
        for close in reversed(closers):
            proof = close(proof, goal)
        unproved = self.unproved_requires()
        if unproved:
            raise self.defect(
                unproved[0],
                f'the requires lines at '
                f'{", ".join(str(n) for n in unproved)} were never proved '
                f'from their reasons')
        return goal, terms, proof

    def respelt(self, proof, said, want, scope):
        """A proof of a claim, made a proof of it spelt another way.

        Two places in a proof may bind one name under two words, because
        each is written where different words were already taken. What is
        proved is the same claim, and `renaming` is what says so.
        """
        if said == want:
            return proof
        apart = self.renaming(self.to_term(said), self.to_term(want))
        if apart is None:
            apart = self.renaming_apart(said, want)
        if apart is None:
            return None
        return self.seq(scope, said, want, proof,
                   self.seq(self.seq(said, want, 'wb'), scope, apart, 'a1i'), 'mpbid')

    def renaming_apart(self, said, want):
        """`renaming` by way of letters neither statement holds.

        `renaming` changes the outer binder first, restating the body it
        wants at the old letter, and that is wrong where the old letter is
        bound again further in: `elcncf2` binds x outside and w inside,
        and the page binds c′ outside and x inside, so restating the page's
        body with x for c′ puts two binders on one letter. Every letter the
        first statement binds is moved to one nothing holds, and the
        statement is renamed from there, where nothing can be caught.

        The letters are only looked at, not taken. They stand in the middle
        of one closed equivalence and nowhere else, and this is tried
        wherever a plain renaming fails, which taking them each time would
        spend the proof's spare letters on.
        """
        held = ({t.split()[0] for t in self.names.values()
                 if isinstance(t, str) and t.endswith(' cv')}
                | self.reserved | set(self.bound_as.values())
                | set(said.split()) | set(want.split()))
        free = iter(v for v in self.spare if v not in held)
        moved, rest = {}, [self.to_term(said)]
        while rest:
            node = rest.pop()
            if node.label in rules.BOUND and len(node.children) >= 2:
                letter = node.children[1].variable
                if letter is not None and letter not in moved:
                    fresh = next(free, None)
                    if fresh is None:
                        return None
                    moved[letter] = kernel.Term(
                        variable=self.sigs[fresh].statement[1])
            rest.extend(node.children)
        if not moved:
            return None
        middle = self.to_term(said).substitute(moved)
        there = self.renaming(self.to_term(said), middle)
        back = self.renaming(middle, self.to_term(want))
        if there is None or back is None:
            return None
        return self.ap('bitri', {'ph': said, 'ps': middle.rpn(self.flabel),
                                 'ch': want}, there, back)

    def letters_apart(self, label, goal, scope, facts, step, crossing, seed):
        """A lemma that binds two letters apart, where the claim binds one.

        `fsumshft` re-indexes a sum and names the index j on one side and k
        on the other, and keeps them apart; the page writes k on both, as
        a reader does, since what a sum binds is no part of what it is. So
        the sum on the right is renamed to a letter nothing holds, the
        lemma proves that, and `cbvsumv` says the two sums are one. The
        letter is only looked at, not taken: it stands in this proof and
        nowhere else.
        """
        if goal.label != 'wceq' or goal.children[1].label != 'csu':
            return Declined(f'{label} binds two letters apart where the claim '
                            f'binds one, and the claim is not an equation '
                            f'with a sum on its right')
        left, right = goal.children
        limits, summand, index = right.children
        held = ({t.split()[0] for t in self.names.values()
                 if isinstance(t, str) and t.endswith(' cv')}
                | self.reserved | set(self.bound_as.values())
                | set(goal.rpn(self.flabel).split()))
        free = next((v for v in self.spare if v not in held), None)
        if free is None:
            return Declined('no letter left to rename a sum with')
        letter = kernel.Term(variable=self.sigs[free].statement[1])
        moved = summand.substitute({index.variable: letter})
        renamed = kernel.Term('csu', (limits, moved, letter))
        first = self.apply_lemma(
            label, kernel.Term('wceq', (left, renamed)), scope, facts, step,
            crossing, seed)
        if declined(first):
            return first
        tie = self.prove_essential(
            kernel.Term('wi', (kernel.Term('wceq', (
                kernel.Term('cv', (letter,)), kernel.Term('cv', (index,)))),
                kernel.Term('wceq', (moved, summand)))), scope, facts)
        if declined(tie):
            return tie
        same = self.ap('cbvsumv', {'j': letter.rpn(self.flabel),
                                   'k': index.rpn(self.flabel),
                                   'A': limits.rpn(self.flabel),
                                   'B': moved.rpn(self.flabel),
                                   'C': summand.rpn(self.flabel)}, tie)
        was, now = renamed.rpn(self.flabel), right.rpn(self.flabel)
        return self.ap('eqtrd', {'ph': scope, 'A': left.rpn(self.flabel),
                                 'B': was, 'C': now},
                       first, self.seq(self.seq(was, now, 'wceq'), scope,
                                       same, 'a1i'))

    def page_spelt(self, said, scope):
        """What a lemma says, put in the page's words, and why they agree.

        `elcncf2` says continuity with ε and δ in ℝ⁺, and the page says
        ε ∈ ℝ with ε > 0. `rules.SPELLINGS` holds set.mm's statements that
        those are the same, and each is applied wherever its left side
        stands, under however many binders, the innermost first so that
        what an outer one reads is already the page's.

        Gives back the new statement and a proof, under the scope, that it
        and the old one are equivalent. Where nothing is spelt differently
        the statement comes back as it was, and there is nothing to prove.
        """
        old = self.to_term(said)
        new = self.in_page_words(old)
        want = new.rpn(self.flabel)
        if want == said:
            return said, None

        def respelt_here(given, wanted, where, held):
            for label in rules.SPELLINGS:
                reads = self.syntax.statement(self.sigs[label])
                names = reads.names()
                ours = kernel.match(reads.children[0], given, {}, names)
                theirs = kernel.match(reads.children[1], wanted, {}, names)
                if ours is None or theirs is None \
                        or ours['x'].rpn(self.flabel) \
                        != theirs['x'].rpn(self.flabel):
                    continue
                # The body is put in the page's words first, under set.mm's
                # own quantifier, and the spelling then changes the
                # quantifier around a body both sides already share.
                middle = reads.children[0].substitute(theirs)
                closed = self.ap(label, self.spelt(theirs))
                turned = self.seq(self.seq(middle.rpn(self.flabel),
                                           wanted.rpn(self.flabel), 'wb'),
                                  where, closed, 'a1i')
                if middle.rpn(self.flabel) == given.rpn(self.flabel):
                    return turned
                inside = self.congruence(given, middle, where, held, None,
                                         respelt_here)
                if declined(inside):
                    return inside
                return self.seq(where, given.rpn(self.flabel),
                                middle.rpn(self.flabel),
                                wanted.rpn(self.flabel), inside, turned,
                                'bitrd')
            return None

        alike = self.congruence(old, new, scope, {}, None, respelt_here)
        if declined(alike):
            return alike
        return want, alike

    def in_page_words(self, term):
        """The statement with every spelling applied, innermost first."""
        if term.variable is not None or not term.children:
            return term
        term = kernel.Term(term.label,
                           tuple(self.in_page_words(c) for c in term.children))
        for label in rules.SPELLINGS:
            reads = self.syntax.statement(self.sigs[label])
            bound = kernel.match(reads.children[0], term, {}, reads.names())
            if bound is not None:
                return reads.children[1].substitute(bound)
        return term

    def step(self, step, scope, facts, lines, closers):
        """One step, with the search offered only what the step names."""
        number = '.'.join(str(p) for p in step.number)
        with self.resting_on(frozenset(self.named(step, number))):
            return self.one_step(step, number, scope, facts, lines, closers)

    def one_step(self, step, number, scope, facts, lines, closers):
        head = step.just.head
        self.last = number
        self.at = step.line
        if head == 'obtain':
            return self.obtain(step, number, scope, facts, lines, closers)
        node = self.read(self.sentences(' '.join(step.claim))[-1])
        term = self.claim_of(' '.join(step.claim))
        how = {'algebra': self.algebra, 'arithmetic': self.arithmetic,
               'inequalities': self.inequalities,
               'substitute': self.substitute,
               'instantiate': self.instantiate,
               'calculation': self.calculation, 'join': self.join,
               'exhibit': self.exhibit}.get(head)
        if how is None and head.startswith('def:'):
            item = self.item_cited(head)
            # A definition stated as a biconditional is used by unfolding it;
            # one stated as an equation is used by citing the lemma that
            # proves it. With no target it is taken as stated, like a closure
            # method, and listed at the file's head.
            if 'target' not in item.fields:
                how = self.take_definition
            elif any('↔' in text for text, _line in item.conclusions):
                how = self.reading(item, term)
            else:
                how = self.unfold_equation
        if how is None and head.startswith('thm:'):
            how = self.cite
        if how is None:
            raise self.defect(step.line, f'no expansion for {head!r}')
        # The step's own requires lines hold for the whole of it, not only
        # for the helpers that ask `supplied` themselves. A membership asked
        # while turning an equation round in `def:stdlib/divisibility/divides`
        # is as much the step's as one asked by the lemma it cites, and the
        # line the page wrote for it is the one to use. Offered as `written`
        # is, which the membership lookup and the one-lemma bridge read and a
        # search does not, so what `settle` searches is no wider.
        kept = self.written
        if step.requires:
            known = self.supplied(step, scope, facts)
            self.written = {**kept, **{
                k: (scope, v) for k, v in known.items()
                if any(o.startswith(REQUIRES)
                       for o in getattr(v, 'origin', ()))}}
        citing, self.citing = self.citing, frozenset(step.just.refs)
        try:
            proof = how(step, node, term, scope, facts, lines)
        finally:
            self.written, self.citing = kept, citing
        # Every route the method had declined, so nothing here owns the
        # step. That is this elaborator's limit rather than a defect in the
        # text, and it is said here because here is where the step is.
        if declined(proof):
            raise self.defect(step.line,
                              f'no method owns this step: {proof}')
        if proof is None:                  # a join, which emits nothing
            return scope, facts, closers
        said = self.said(step)
        self.rests_on_named(proof, self.named(step, number), step.line,
                            f'step {number}')
        self.does_work(step, number, proof)
        proof = self.seal(proof, number)
        lines[number] = Fact(term, proof, said)
        facts[term] = proof
        # A line saying several things says each of them: Bezout's step 15
        # states what a gcd is in four sentences and its step 17 wants the
        # first of them. Only as deep as the sentences the text wrote —
        # `claim_of` conjoined those, and splitting further would take
        # apart what one sentence says and offer the pieces as lines.
        if len(said) > 1:
            self.unpack(term, proof, scope, facts, depth=len(said) - 1)
        return scope, facts, closers

    # --- the methods --------------------------------------------------------

    def cite_item(self, step, goal, scope, facts, item, cites=None):
        """What an item states, however the database says it is supplied.

        An item with no target is assumed: nothing in the library has its
        shape, and the file says so at its head. An item that has one and
        whose every clause misses is a different thing, and is an error.
        The field says where the claim lands, and it does not land there.

        Assuming it instead would give the same file, the same assumption
        count and no message, so a target that can never fire would read
        exactly like a target nobody wrote.
        """
        # An item this corpus proves is applied the way a cited one is,
        # however the step reaches it: `obtain` asks for the existence its
        # statement claims, and `thm:proof/sqrt2-irrational/lowest-terms` is
        # proved here.
        if proved(item):
            return self.cite_corpus(step, goal, scope, facts, None, item,
                                    cites)
        labels = targets.clauses(item)
        seed = self.filling(step, item, cites)
        for label in labels:
            found = self.apply_lemma(label, self.to_term(goal), scope, facts,
                                     step, seed=seed)
            if not declined(found):
                return found
        assembled = self.from_lemmas(labels, goal, scope, facts, step, seed)
        if not declined(assembled):
            return assembled
        if labels:
            # The item is reached from an `obtain` or from a requires line
            # naming it, so `step.just.head` is not the item, and the item
            # names itself. The labels it named say which field to look at,
            # and what they did not reach is said as it stands.
            kind = 'def' if item.kind == 'definition' else 'thm'
            wanted = (f'what step {fmt(step.number)} obtains'
                      if step.just.head == 'obtain'
                      else self.render(self.to_term(goal).rpn(self.flabel)))
            raise self.defect(step.line,
                              f'{kind}:{qualified(item)} targets '
                              f'{", ".join(labels)}, and none of them reaches '
                              f'{wanted}')
        return self.assume_item(step, goal, scope, facts, item, cites)

    def assume_item(self, step, goal, scope, facts, item, cites=None):
        """An item the database gives no target for, taken as it states itself.

        `thm:proof/sqrt2-irrational/lowest-terms` is the case: set.mm has
        nothing of its shape, as its `note` says, so what it claims is assumed
        under the hypotheses it asks for.
        """
        saved = dict(self.names)
        for name, node in self.item_binding(step, item, cites).items():
            self.names[name] = self.term(node)
        asks = []
        with self.in_its_names(item):
            for kind, text, _label, _line in item.hypotheses:
                body = hypothesis_body(kind, text)
                asks.append(self.term(self.read(body)))
            ends = [self.term(self.read(text))
                    for text, _line in item.conclusions]
        self.names = saved

        # What is assumed is what the item states, and a step may claim one
        # side of it: `thm:stdlib/numbers/abs-difference-lt` says |x − c| < δ
        # exactly when c − δ < x and x < c + δ, and step 17.11 of the intermediate value
        # proof claims the first from lines saying the second. Stating the
        # claim under the item's hypotheses alone would assume that every
        # |x − c| is below every δ.
        whole = ends[0]
        for extra in ends[1:]:
            whole = self.seq(whole, extra, 'wa')
        other = None
        if self.rebound(whole, goal):
            whole = goal
        if whole != goal:
            node = self.to_term(whole)
            sides = ([c.rpn(self.flabel) for c in node.children]
                     if node.label == 'wb' else [])
            # A side binding other letters than the claim is the claim, as
            # the whole is above, and is stated in the claim's letters:
            # step 16 of the intermediate value proof unfolds continuity
            # over c′ where the definition says c.
            for i, side in enumerate(sides):
                if side != goal and self.rebound(side, goal):
                    sides[i] = goal
                    whole = self.seq(*sides, 'wb')
            if goal not in sides:
                kind = 'def' if item.kind == 'definition' else 'thm'
                raise self.defect(
                    step.line,
                    f'{kind}:{qualified(item)} is taken as stated and states '
                    f'{self.render(whole)}, where step {fmt(step.number)} '
                    f'claims {self.render(goal)}')
            other = sides[1 - sides.index(goal)]

        statement = whole
        for one in reversed(asks):
            statement = self.seq(one, statement, 'wi')
        label = self.fresh('itm')
        text = '|- ' + self.render(statement)
        self.axioms.append((label, text))
        free = sorted({t for t in text.split() if t in self.flabel},
                      key=lambda v: self.forder[self.flabel[v]])
        self.sigs[label] = Signature(
            label, '$a', text.split(),
            [(self.sigs[self.flabel[v]].statement[0], v) for v in free])
        proof = self.seq(*(self.flabel[v] for v in free), label)
        # An item taken as stated asks for its hypotheses like any other,
        # and a hypothesis a reader would not write as a line is written as
        # a `requires`: the subsets proof adds an element back to the set it
        # was removed from and says `requires a ∉ X ∖ {a}`.
        known = self.with_cited(step, scope,
                                self.supplied(step, scope, facts))
        if not asks:
            proof = self.seq(whole, scope, proof, 'a1i')
        for i, one in enumerate(asks):
            rest = whole
            for later in reversed(asks[i + 1:]):
                rest = self.seq(later, rest, 'wi')
            # With the step, so a "there is" it asks can be given by an
            # instance a cited line names: `thm:stdlib/calculus/completeness`
            # asks that S be bounded above, and the step cites that b is an upper bound.
            supplied = self.settle(self.to_term(one), scope, known,
                                   step=step, lines=self.lines)
            # The item is assumed because the database points at nothing for
            # it, and the head of the file says so. Its hypotheses are a
            # different matter: they are stated, and a step citing the item
            # owes them. One that cannot be settled is the step asking for
            # the claim and paying nothing for it, which would widen what
            # the file assumes without adding a line to the list that says
            # what it assumed.
            if declined(supplied):
                kind = 'def' if item.kind == 'definition' else 'thm'
                raise self.defect(
                    step.line,
                    f'{kind}:{qualified(item)} is taken as stated and asks for '
                    f'{self.render(one)}, which step {fmt(step.number)} does '
                    f'not supply: {supplied}')
            proof = self.seq(scope, one, rest, supplied, proof,
                        'syl' if i == 0 else 'mpd')
        if other is None:
            return proof
        # The side the step does not claim is what it cites, a line whole or
        # one line per conjunct.
        node = self.to_term(other)
        pair = ([c.rpn(self.flabel) for c in node.children]
                if node.label == 'wa' else [])
        if other in known:
            given = known[other]
        elif pair and all(p in known for p in pair):
            given = self.seq(scope, *pair, *(known[p] for p in pair), 'jca')
        else:
            raise self.defect(step.line,
                              f'step {fmt(step.number)} cites nothing that '
                              f'says {self.render(other)}')
        if goal == self.to_term(whole).children[0].rpn(self.flabel):
            return self.seq(scope, goal, other, given, proof, 'mpbird')
        return self.seq(scope, other, goal, given, proof, 'mpbid')

    def item_binding(self, step, item, cites=None):
        """What an item's names stand for at this step, as the page says it.

        A name the step writes, `v := t`, first. Then the item's conclusion
        matched against the step's claim, and each of its hypotheses against
        what the step cites, until nothing more is learned — which is how
        `check.py` reads a citation, done here so an item taken as stated is
        stated about the step's things: `thm:stdlib/functions/function-value`
        says `let x ∈ D`, and the intermediate value proof has no D. A name
        nothing fixes is read as the proof's own letter.
        """
        bound = {}
        for name, value in instantiation(cites or step.just.text):
            bound[name] = self.read(value)
        with self.in_its_names(item):
            ends = [self.read(text) for text, _line in item.conclusions]
            hyps = [self.read(hypothesis_body(kind, text))
                    for kind, text, _label, _line in item.hypotheses]
        binders, props = binding_context(self.g.notations)
        # A name the item binds itself is the item's own and stands for
        # nothing at the step: continuity's c runs over D, and matched
        # against the step's claim it would be bound to the step's c′,
        # which is nothing outside its own binder either.
        own = set()
        rest = [*ends, *hyps]
        while rest:
            node = rest.pop()
            shape = binders.get(node.notation)
            if shape and node.children[shape[0]].notation == 'name':
                own.add(node.children[shape[0]].text)
            rest.extend(node.children)
        variables = set().union(*(names_in(n) for n in [*ends, *hyps])) - own
        # A definition is a biconditional, and a step unfolding one claims
        # one side and cites the other: `def:stdlib/calculus/continuous-on` from "f is
        # continuous on [a, b]" is what says D is [a, b]. So each side is
        # matched as well as the whole, the claim against either and the
        # cited lines against either.
        sides = [side for end in ends if end.notation == 'biconditional'
                 for side in end.children]
        hyps = [*hyps, *sides]
        for end in [*ends, *sides]:
            for said in self.said(step):
                got = match(end, said, bound, variables, props)
                if got is not None:
                    bound = got
                    break
        given = []
        for ref in step.just.refs:
            if ref in self.lines:
                given += list(self.lines[ref].sentences)
        # Only what the step cites. A sort line fixes nothing: every set in
        # scope is a set, and `let X be a set` matched against the first one
        # bound the subsets proof's X to its A.
        given += [self.read(hypothesis_body(kind, text))
                  for kind, text, label, _line in self.thm.hypotheses
                  if label in step.just.refs]
        learned = True
        while learned:
            learned = False
            for hyp in hyps:
                for fact in given:
                    got = match(hyp, fact, bound, variables, props)
                    if got is not None and len(got) > len(bound):
                        bound, learned = got, True
                        break
        return bound

    def instantiate(self, step, node, term, scope, facts, lines):
        """A universal used at one term.

        `instantiate s := a in line 10` takes a line claiming something of
        every s in a set and claims it of one of them. What the lemma wants
        beyond the line is that the term is in the set, and the step writes
        that: in `from` where a line already says it, in `requires` where it
        has to be built, so it is asked for through `required` and not
        settled behind the text's back.

        set.mm asks `( x = A -> ( ph <-> ps ) )` of it, which is the same
        thing `elrab` and `rspcev` ask, so what `ps` is is worked out from
        the body rather than taken from anywhere.
        """
        where = step.just.target
        held = lines.get(where)
        if held is None:
            raise self.defect(step.line,
                              f'instantiate names no line or label {where!r}')
        # A line may say several things at once, and the `for every` is
        # rarely the first of them: Bezout's line 15 says four and
        # quantifies in the fourth. Unpacking makes each a fact of its own.
        # Taken apart on its own, so each part is the cited line's and not
        # a copy of the same claim the scope holds from another line.
        known = {held.term: self.carried(where, facts, lines)}
        self.unpack(held.term, known[held.term], scope, known)
        universals = [p for p in self.parts(held.term)
                      if self.to_term(p).label in ('wral', 'wal')]
        # The universal is the one binding the name the step instantiates.
        # A line may hold two: the intermediate value proof's line 9 says c
        # is an upper bound, which is `for every s ∈ S`, and then `for every
        # u ∈ ℝ`, and step 12 instantiates u.
        named = [name for name, _value in instantiation(step.just.text)]
        bound = {self.bound_as.get(n) or self.flabel.get(n) for n in named}
        said = next((p for p in universals
                     if self.to_term(p).children[1].rpn(self.flabel) in bound),
                    universals[0] if universals else None)
        if said is None:
            raise self.defect(step.line,
                              f'{where} claims nothing of every such name')

        proof, whole = known[said], self.to_term(said)
        for _name, value in instantiation(step.just.text):
            # A name may run over a set or over anything that is one. The
            # two lemmas are the same shape and ask the same thing; what
            # differs is whether the term has to be in a set or only be one.
            if whole.label == 'wral':
                body, variable, over = whole.children
                lemma, slot, domain = 'rspcv', 'B', over.rpn(self.flabel)
            elif whole.label == 'wal':
                body, variable = whole.children
                lemma, slot, domain = 'spcgv', 'V', 'cvv'
            else:
                raise self.defect(step.line,
                                  'more names instantiated than are '
                                  'quantified')
            mark, at = f'{variable.rpn(self.flabel)} cv', \
                self.term(self.read(value))
            instance = self.restated(body, mark, at)
            ph, ps = body.rpn(self.flabel), instance.rpn(self.flabel)
            member = self.seq(at, domain, 'wcel')
            asked = self.prove_essential(
                self.to_term(self.seq(self.seq(mark, at, 'wceq'),
                                 self.seq(ph, ps, 'wb'), 'wi')), scope, facts)
            if declined(asked):
                raise self.defect(step.line,
                                  f'{lemma} cannot tie the line to its '
                                  f'instance: {asked}')
            applied = self.ap(lemma, {
                'ph': ph, 'ps': ps, 'x': variable.rpn(self.flabel),
                'A': at, slot: domain}, asked)
            proof = self.seq(scope, whole.rpn(self.flabel), ps, proof,
                        self.seq(scope, member,
                            self.seq(whole.rpn(self.flabel), ps, 'wi'),
                            self.required(step, member, domain, scope, facts),
                            applied, 'syl'),
                        'mpd')
            whole = instance

        # What a universal says of one name is often a conditional, and the
        # step claims what it concludes. Each thing asked on the way is a
        # line the step cites.
        reached = whole.rpn(self.flabel)
        while reached != term:
            reads = self.to_term(reached)
            if reads.label != 'wi':
                raise self.defect(step.line,
                                  f'{where} at those terms says '
                                  f'{self.render(reached)}, and the step '
                                  f'claims {self.render(term)}')
            asks, rest = (c.rpn(self.flabel) for c in reads.children)
            # An `instantiate` is the head of a step and not a route among
            # several, so what the universal asks at this term is the
            # text's to supply: `SYNTAX.md` says the step writes it, in
            # `from` where a line already says it and in `requires` where
            # none does.
            supplied = self.settle(self.to_term(asks), scope, facts)
            if declined(supplied):
                raise self.defect(
                    step.line,
                    f'instantiating at that term wants {self.render(asks)}, '
                    f'which step {fmt(step.number)} does not supply: '
                    f'{supplied}')
            proof = self.seq(scope, asks, rest, supplied, proof, 'mpd')
            reached = rest
        return proof

    def substitute(self, step, node, term, scope, facts, lines):
        """One equation put into one claim, at the place the tree names.

        The claim rewritten is the step's own unless the line says otherwise:
        `into line 1` points the congruence at a line already proved, which
        is `ELABORATION.md` requirement 11. The two differ in what comes out —
        rewriting inside a claim gives an equation between the two readings,
        rewriting a whole claim gives a biconditional — so what closes them
        differs too.
        """
        # The reference is a bracket near the end; the equation may hold
        # brackets of its own, as `S(k) = k(k + 1)/2` does, and `into` may
        # follow, as `substitute √2 = p/q (line 3.1) into line 1` does.
        # A direction is not part of what the line says, so a line that
        # writes one is read the same as a line that does not. `GRAMMAR.md`
        # allows the marker because it tells a reader which way the author
        # had in mind.
        text = re.sub(r',\s*right to left\s*$', '', step.just.text).strip()
        said = re.match(r'substitute\s+(.*)\s*\(([^()]*)\)'
                        r'(?:\s+into\s+(\S.*?))?\s*$', text)
        if said is None:
            raise self.defect(step.line,
                              'a substitute that names no equation')
        left, right = self.read(said.group(1)).children
        old, new = self.term(left), self.term(right)
        # Which way the equation faces in the kernel is the lemma's choice,
        # not the text's, so either is accepted and turned if it has to be.
        # An equation of numerals alone the page may take from `arithmetic`
        # where it rewrites by it, and it is proved here, in place.
        facing = facts.get(self.seq(old, new, 'wceq'))
        if said.group(2).strip() == 'arithmetic':
            facing = self.closed_fact(
                self.seq(old, new, 'wceq'), scope, facts,
                f'step {fmt(step.number)} substitutes {said.group(1).strip()}',
                step)
        if facing is None:
            held = facts.get(self.seq(new, old, 'wceq'))
            if held is None:
                raise self.defect(step.line,
                                  f'no equation {old} = {new} in scope')
            facing = self.seq(scope, new, old, held, 'eqcomd')
        turned = self.seq(scope, old, new, facing, 'eqcomd')

        if said.group(3) is None:
            # An equation is one fact and a claimed equation is one fact, and
            # neither carries a direction: if a = b then b = a. So the cited
            # equation is read whichever way rewrites, and the step's own two
            # sides whichever way one reaches the other. Which side is
            # written first decides nothing, and a proof needs no marker
            # saying so. What comes out proves the claim as the step states
            # it, turned by `eqcomd` where it was reached the other way.
            sides = ((node.children[0], node.children[1], False),
                     (node.children[1], node.children[0], True))
            for was, now, faces in ((old, new, facing), (new, old, turned)):
                for start, other, flip in sides:
                    made = self.rewrite(start, was, now, scope, faces)
                    if declined(made):
                        continue
                    built, proof = made
                    if built != self.term(other):
                        continue
                    return self.seq(scope, self.term(start), self.term(other),
                               proof, 'eqcomd') if flip else proof
            raise self.defect(step.line,
                              'the substitution misses the claim')

        where = said.group(3).split()[-1]
        into = lines[where]
        if not into.sentences:
            raise self.defect(step.line,
                              f'{said.group(3)} is not a line to rewrite')
        # A line may say several things and the substitution land in one of
        # them: bezout obtains a quotient and a remainder and three facts
        # about them on one line, and rewrites the third. So each sentence
        # is offered with a proof of itself, which `unpack` has already
        # taken apart, and the whole line is one of them.
        held = self.carried(where, facts, lines)
        known = {into.term: held}
        self.unpack(into.term, held, scope, known)
        # Which way the equation is used is whichever reaches what the step
        # claims. Cantor puts f(x) = B into a line saying x ∉ f(x) and into
        # another saying x ∉ B, and writes the equation once; and B holds an
        # f(x) of its own, under a name it binds, that neither touches.
        for was, now, faces in ((old, new, facing), (new, old, turned)):
            for one in into.sentences:
                start = self.term(one)
                if start not in known:
                    continue
                made = self.rewrite(one, was, now, scope, faces)
                if declined(made):
                    continue
                built, proof = made
                if built == term:
                    return self.seq(scope, start, term, known[start], proof,
                               'mpbid')
        raise self.defect(step.line, 'the substitution misses the claim')

    def equivalent(self, step, node, term, scope, facts, lines):
        """A definition whose right side is not an existence claim.

        `def:stdlib/numbers/irrational` says x is irrational exactly when x is
        real and not rational, and the step cites the two lines that say each. The lemma
        gives the biconditional and the lines give its right side, so the
        definition is read the way the text reads it: right to left.
        """
        item = self.item_cited(step.just.head)
        return self.trying(item, step, self.one_equivalent, term, scope,
                           facts, lines)

    def one_equivalent(self, lemma, step, term, scope, facts, lines):
        # What a lemma's right side says beyond what its left fixes can
        # only come from the lines the step cites, offered in the order the
        # step writes them.
        said = [lines[ref].term for ref in step.just.refs if ref in lines]
        hint = said[0] if said else None
        for extra in said[1:]:
            hint = self.seq(hint, extra, 'wa')
        # No name is introduced here: the claim already carries whatever the
        # lemma binds, and the match is what says which variable that is.
        made = self.unfolding(step, lemma, term, None, None, None,
                              scope, facts, hint=hint)
        if declined(made):
            return made
        says, right = made
        # The right side is what the step supplies, its requires lines and
        # the lines it cites, and not whatever the scope would give: step 1
        # of the intermediate value proof writes `a ≤ b` for
        # `def:stdlib/calculus/interval`, and the scope would build it from
        # a < b behind the line's back.
        known = self.with_cited(step, scope,
                                self.supplied(step, scope, facts))
        under = self.settle(self.to_term(right), scope, known,
                            step=step, lines=lines)
        if declined(under):
            return under
        return self.seq(scope, term, right, under, says, 'mpbird')

    def turned(self, rpn):
        """The same two-sided claim with its sides the other way round."""
        node = self.to_term(rpn)
        if len(node.children) != 2:
            return None
        return self.seq(node.children[1].rpn(self.flabel),
                   node.children[0].rpn(self.flabel), node.label)

    def unfolded(self, step, node, term, scope, facts, lines):
        """A definition unfolded to reach one part of what it says.

        `def:stdlib/sets/set-builder` says that belonging to {t ∈ X : P(t)} is belonging
        to X and having the property, and Cantor's step 3.1.3.1 wants the
        second of those from a line that says the first. So the definition
        is read left to right and what it gives is taken apart.
        """
        item = self.item_cited(step.just.head)
        return self.trying(item, step, self.one_unfolded, term, scope, facts,
                           lines)

    def one_unfolded(self, lemma, step, term, scope, facts, lines):
        sig = self.sigs[lemma]
        whole = self.syntax.statement(sig)
        variables, reads = whole.names(), whole
        while reads.label == 'wi':
            reads = reads.children[1]
        if reads.label != 'wb':
            return Declined(f'{lemma} states no biconditional')
        # A line may say several things at once, and what the definition
        # unfolds is any one of them: the primes proof obtains a natural
        # number, its primality and what it divides on a single line, and it
        # is the middle conjunct that `isprm2` unfolds.
        for ref in step.just.refs:
            cited = lines.get(ref)
            if cited is None:
                continue
            held = {cited.term: self.carried(ref, facts, lines)}
            # The term kept for a line is its last sentence, and a line
            # saying several things says the others just as much: Bezout's
            # line 5 hands over a d in S and what is least about it, and it
            # is the first of the two that `elrab` unfolds.
            for one in cited.sentences:
                said = self.term(one)
                if said in facts:
                    held.setdefault(said, facts[said])
            self.unpack(cited.term, held[cited.term], scope, held)
            for said, shown in held.items():
                binding = kernel.match(reads.children[0], self.to_term(said),
                                       {}, variables)
                if binding:
                    given = shown
                    break
            else:
                continue
            break
        else:
            return Declined(f'no cited line is what {lemma} unfolds')
        # What the left side fixes need not be everything the right side
        # holds: `rabid` learns the property from the claim itself.
        for part in self.parts(reads.children[1].rpn(self.flabel)):
            filled = kernel.match(self.to_term(part), self.to_term(term),
                                  dict(binding), variables)
            if filled is not None:
                binding = filled
                break
        # The claim is one of those parts, so a claim of the membership
        # half leaves the property half standing as the lemma's own name.
        # `elrab`'s hypothesis is then what says what that half is, and it
        # is the only thing that does: nothing on the left mentions it.
        for essential in sig.essentials:
            more = self.substituted_slot(
                self.syntax.parse(essential[1:], 'wff'), binding)
            if more is not None:
                binding = {**binding, **more}

        left = reads.children[0].substitute(binding).rpn(self.flabel)
        right = reads.children[1].substitute(binding).rpn(self.flabel)
        made = self.unfolding(step, lemma, left, right, None, None,
                              scope, facts)
        if declined(made):
            return made
        proof = self.seq(scope, left, right, given, made[0], 'mpbid')
        known = {right: proof}
        self.unpack(right, proof, scope, known)
        if term in known:
            return known[term]
        # Or it is, once what the lemma says is put in the page's words and
        # the letters it binds are the step's: `elcncf2` gives continuity
        # over ℝ⁺ with its own x, y, z and w.
        for said, shown in list(known.items()):
            got = self.page_spelt(said, scope)
            if declined(got) or got[0] == said:
                continue
            new, alike = got
            carried = self.seq(scope, said, new, shown, alike, 'mpbid')
            spelt = self.respelt(carried, new, term, scope)
            if spelt is not None:
                return spelt
        # What the unfolding says and how the readable line spells it are
        # allowed to differ, so long as set.mm says they are the same claim:
        # `isprm2` writes p > 1 as membership of ZZ>=2, and `eluz2gt1` is
        # the declared lemma that carries one to the other.
        # Only a route declining is turned into this lemma declining. A
        # defect `settle` found on the way — a step citing no witness, say —
        # is a person's to fix and goes past, where it used to be reworded
        # as this and lost.
        found = self.settle(self.to_term(term), scope,
                            {**facts, **known}, step=step, lines=lines)
        if declined(found):
            return self.no(f'{lemma} does not say {{}}: {found}', term)
        return found

    def trying(self, item, step, way, term, scope, facts, lines):
        """Use whichever lemma the target names reaches the claim.

        A definition may be supplied by more than one, differing in what
        they ask: `rabid` says what belongs to a set-builder when the
        element is the name the builder binds, and `elrab` when it is
        anything else, and only one of the two can be right of any step.

        A defect the way found on its own account is not one of the lemmas
        declining, and goes past. It used to be caught here with them and
        kept in `trouble`, which meant a proof whose later lemma happened to
        fit was accepted with the defect in it and nothing said so.
        """
        declines = []
        for lemma in targets.clauses(item):
            found = way(lemma, step, term, scope, facts, lines)
            if not declined(found):
                return found
            declines.append(str(found))
        return Declined('; '.join(declines) if declines
                        else f'{qualified(item)} targets nothing')

    def reading(self, item, term):
        """Which of three ways a biconditional definition reaches a claim.

        The claim decides, and what the lemma states decides with it. A
        definition reaching an existence claim supplies a witness; one whose
        right side the step already holds is read right to left; one whose
        left side the step holds is unfolded and taken apart.

        Every lemma the target names is asked, not just the first: `rabid`
        and `elrab` say the same thing of a set-builder and differ only in
        what they ask, so which of the two fits says nothing about which
        way the definition is being read.
        """
        for lemma in targets.clauses(item):
            whole = self.syntax.statement(self.sigs[lemma])
            while whole.label == 'wi':
                whole = whole.children[1]
            if whole.label != 'wb' or whole.children[1].label == 'wrex':
                return self.conclude
            if kernel.match(whole.children[0], self.to_term(term), {},
                            whole.names()) is not None:
                return self.equivalent
        return self.unfolded

    def take_definition(self, step, node, term, scope, facts, lines):
        """A definition with no target is taken as it states itself.

        Unless a line the step cites already says it. A congruence
        elaborates to the conjunction of the six equations
        `def:stdlib/geometry/congruent` lists, so a step reading one of them
        off names the definition but asks for nothing the file does not have:
        the claim is a conjunct, and `unpack` reaches it.

        Otherwise what is stated is the definition, in its own words and at
        the step's terms, and the claim is read off it by `assume_item` as
        an item's is. Stating the claim itself under the cited lines would
        take whatever the step claimed: continuity with δ where ε belongs
        was taken, and only a later step using it noticed.
        """
        found = self.projected(step, term, scope, facts, lines)
        if found is not None:
            return found
        # Or says it with another letter bound. The notation reads "b is an
        # upper bound of S" as every s in S being at most b, and the block
        # that proved it for every s fixed a variable of its own, so the
        # line and the claim differ only in the letter.
        for ref in step.just.refs:
            held = lines.get(ref)
            if held is None:
                continue
            parts = {held.term: self.carried(ref, facts, lines)}
            self.unpack(held.term, parts[held.term], scope, parts)
            for said, proof in parts.items():
                spelt = self.respelt(proof, said, term, scope)
                if spelt is not None:
                    return spelt
        return self.assume_item(step, term, scope, facts,
                                self.item_cited(step.just.head))

    def projected(self, step, term, scope, facts, lines):
        """The claim, when a line the step cites is a conjunction stating it.

        The depth is the six conjuncts of a congruence, which nest to the
        left, so reaching the first of them costs five.
        """
        for ref in step.just.refs:
            cited = lines[ref]
            # The cited line taken apart on its own. Taken apart into the
            # scope, a part the scope already holds is kept as the scope has
            # it: line 8 of the intermediate value proof says c is a least
            # upper bound, which holds that c is an upper bound, and step 10
            # citing line 9 for it got line 8's.
            known = {cited.term: self.carried(ref, facts, lines)}
            self.unpack(cited.term, known[cited.term], scope, known, depth=8)
            if term in known:
                return known[term]
        return None

    def unfold_equation(self, step, node, term, scope, facts, lines):
        """A definition stated as an equation, one clause per `then` group.

        `def:stdlib/sums/S` says what S(1) is and what S(n + 1) is, and set.mm
        proves each separately. The clause is chosen by which lemma's conclusion is what
        the step claims, so the text never says which.

        A clause that declines is a clause that is not this `then` group,
        and the next one is asked. What it is not is the elaborator's own
        limit: the database named these lemmas, so a step none of them
        reaches is a step claiming what the definition does not say, and
        that is a defect rather than a decline.
        """
        item = self.item_cited(step.just.head)
        found = self.by_clause(targets.split_entries(item.fields['target']),
                               term, scope, facts, step,
                               self.filling(step, item))
        if declined(found):
            raise self.defect(step.line,
                              f'no clause of {step.just.head} gives what step '
                              f'{fmt(step.number)} claims')
        return found

    def through_existential(self, label, whole, reads, goal, scope, facts,
                            step, seed):
        """A lemma's existential taken apart, and the claim's put back.

        `divalg` says there is exactly one remainder, quantified the other
        way round, bounding by the absolute value, and saying its three
        things in a different order. The division algorithm as a reader
        writes it says the same. Two of those four differences stop being
        differences once the quantifier is off: in the open `unpack` makes
        the body's parts facts and `settle` puts them back in whatever
        order the claim asks, and there is no order to quantifiers that are
        not there.

        So the lemma's existential is proved, weakened where it says
        exactly one, eliminated, and the claim introduced at the variables
        it gave up. `obtain` does the eliminating for a step, deferring the
        discharge because only the main loop knows a goal; here the goal is
        in hand and nothing is deferred.
        """
        if goal.label != 'wrex' or reads.label not in ('wrex', 'wreu'):
            return Declined(f'{label} and the claim are not both "there is"')
        if seed is None or (reads.names() - set(seed)
                            - set(self.bound_in(reads))):
            return Declined(f'nothing fixes the variables of {label}')
        ground = reads.substitute(seed)
        # The lemma's binders become names in the open, so they must be
        # variables nothing else holds — and the claim's own binders are
        # among what is held, because `rspcev` will not take a witness that
        # mentions the binder it is introducing. `divalg` binds q and r and
        # so does the division algorithm as a reader writes it, which is
        # what makes this not the corner case it looks like.
        taken, swap = self.bound_in(goal), {}
        for name in self.bound_in(ground):
            fresh = self.spare_var()
            while self.sigs[fresh].statement[1] in taken:
                fresh = self.spare_var()
            swap[name] = kernel.Term(variable=self.sigs[fresh].statement[1])
        ground = ground.substitute(swap)
        strong = self.apply_lemma(label, ground, scope, facts, step,
                                  crossing=False, seed=seed)
        if declined(strong):
            return strong
        if ground.label == 'wreu':
            weaker = kernel.Term('wrex', tuple(ground.children))
            body, var, over = ground.children
            strong = self.seq(scope, ground.rpn(self.flabel),
                         weaker.rpn(self.flabel), strong,
                         self.ap('reurex', {'ph': body.rpn(self.flabel),
                                            'x': var.rpn(self.flabel),
                                            'A': over.rpn(self.flabel)}),
                         'syl')
            ground = weaker

        layers, rest = [], ground
        while rest.label == 'wrex':
            _body, var, over = rest.children
            layers.append((var.rpn(self.flabel), over.rpn(self.flabel)))
            rest = _body
        body = rest.rpn(self.flabel)
        member = self.seq(*(self.seq(f'{v} cv', s, 'wcel') for v, s in layers))
        if len(layers) > 1:
            member = self.seq(member, 'wa')

        frame = len(self.frames)
        outer, held = self.widen(scope, facts, member)
        inner, lifted = self.widen(outer, held, body)
        made = self.introduced(goal, inner, lifted)
        del self.frames[frame:]
        if declined(made):
            return made
        want = goal.rpn(self.flabel)
        discharge = 'rexlimdva' if len(layers) == 1 else 'rexlimdvva'
        pushed = [v for v, _s in layers] + [s for _v, s in layers]
        return self.seq(scope, ground.rpn(self.flabel), want, strong,
                   self.seq(scope, body, want, *pushed,
                       self.seq(outer, body, want, made, 'ex'), discharge),
                   'mpd')

    def from_lemmas(self, labels, goal, scope, facts, step, seed):
        """An existence claim its item's lemmas together give.

        `thm:proof/sqrt2-irrational/lowest-terms` says a rational is some p
        over some q with nothing above 1 dividing both. set.mm says that of
        the numerator and denominator it names for a rational, in three
        theorems and no existential at all: what they are is `qnumdencl`, that
        the rational is their quotient is `qeqnumdivden`, and that they are
        coprime is `qnumdencoprm`.

        So each is proved at what the `with` target says it is about, and
        the claim introduced at the terms they turn out to be about. The
        lemmas are the ones the database names and the witnesses are read
        off them, which is what keeps this from being a search.
        """
        if not labels or not seed:
            return Declined('no `with` target says what the lemmas are about')
        want = self.to_term(goal)
        if want.label != 'wrex':
            return Declined('the claim is not "there is"')
        if any(label not in self.sigs for label in labels):
            return Declined(f'{", ".join(labels)} are not all in the library')
        theirs = {v for label in labels for v in self.sigs[label].push}
        witness = [name for name in seed if name not in theirs]
        if witness:
            return self.at_witness(labels, want, seed, witness, scope, facts,
                                   step)
        known = dict(facts)
        for label in labels:
            sig = self.sigs.get(label)
            if sig is None:
                return Declined(f'{label} is not in the library')
            reads = self.syntax.statement(sig)
            while reads.label == 'wi':
                reads = reads.children[1]
            if reads.names() - set(seed):
                return Declined(f'the target does not say what {label} is '
                                f'about')
            said = reads.substitute(seed).rpn(self.flabel)
            proof = self.apply_lemma(label, self.to_term(said), scope, facts,
                                     step, crossing=False, seed=seed)
            if declined(proof):
                return proof
            known[said] = proof
            self.unpack(said, proof, scope, known)
        return self.introduced(want, scope, known)

    def at_witness(self, labels, want, seed, witness, scope, facts, step):
        """An existence claim at the thing a `with` target names for it.

        `thm:stdlib/calculus/completeness` says there is a least upper bound, and set.mm
        names one: the supremum. What the claim asks of it — that it is
        real, that nothing in the set is above it, that it is at most
        anything nothing in the set is above — is one lemma each, and each
        is said of one element or one bound at a time, which `as_generalised`
        says of every one. So the witness is put in for the binder, each
        part of what the claim then says is proved by the first lemma that
        reaches it, and the claim is introduced at the witness.

        A `with` name that is none of the lemmas' variables is what says
        this: it can only be the claim's own binder.
        """
        if len(witness) != 1:
            return Declined(f'the target names {len(witness)} witnesses '
                            f'and the claim is read one binder at a time')
        body, variable, over = want.children
        stood = seed[witness[0]]
        member = self.seq(stood.rpn(self.flabel), over.rpn(self.flabel),
                          'wcel')
        said = self.replaced(body, f'{variable.rpn(self.flabel)} cv', stood)

        def by_lemmas(one):
            refused = []
            for label in labels:
                made = self.apply_lemma(label, one, scope, facts, step)
                if not declined(made):
                    return made
                refused.append(f'{label}: {made}')
            return Declined('; '.join(refused))

        known = dict(facts)
        for part in (self.to_term(member), said):
            made = self.conjoined(part, scope, by_lemmas)
            if made is None:
                made = by_lemmas(part)
            if declined(made):
                return made
            known[part.rpn(self.flabel)] = made
            self.unpack(part.rpn(self.flabel), made, scope, known)
        return self.introduced(want, scope, known)

    def as_class(self, node, marks):
        """A pattern whose binders stand for whatever class fills them.

        A binder is written `cv` over a setvar, which matches a setvar and
        nothing else. What a claim quantifies over may be answered by a
        term — a rational's numerator is one — and the name is the claim's
        way of writing it, not a constraint on what it is.
        """
        if node.variable is not None:
            return node
        if node.label == 'cv' and node.children[0].variable in marks:
            return node.children[0]
        return kernel.Term(node.label, tuple(self.as_class(one, marks)
                                             for one in node.children))

    def introduced(self, goal, scope, facts):
        """An existential claim at witnesses the scope already names.

        `witnessed` does this shape from the lines a step cites. Here the
        witnesses are whatever the elimination just gave up, and which of
        them stands for which binder is read off the body: one part of the
        claim matched against one fact in scope fixes them all, because
        every binder occurs in the part that mentions them.

        A witness may be a term and not a name. `qeqnumdivden` says a
        rational is its numerator over its denominator, and matching a
        claim's `x = p / q` against it is what says that p and q stand for
        those two — so the binder is matched as the class it stands for
        rather than as the name it is written with.
        """
        marks, rest = [], goal
        while rest.label == 'wrex':
            marks.append(rest.children[1].variable)
            rest = rest.children[0]
        found = None
        for piece in self.parts(rest.rpn(self.flabel)):
            shape = self.as_class(self.to_term(piece), set(marks))
            for said in facts:
                fits = kernel.match(shape, self.to_term(said), {}, set(marks))
                if fits is not None and len(fits) == len(marks):
                    found = fits
                    break
            if found is not None:
                break
        if found is None:
            return Declined('no fact in scope names what the claim binds')
        # What each binder stands for, as `rspcev` wants it: a class. One
        # matched where it was written keeps the `cv` that made it one.
        stood = {}
        for name, term in found.items():
            said = term.rpn(self.flabel)
            stood[name] = (self.seq(said, 'cv')
                           if term.variable is not None else said)

        layers, rest = [], goal
        while rest.label == 'wrex':
            body, var, over = rest.children
            layers.append((body, var.variable, over.rpn(self.flabel)))
            rest = body

        proof = None
        for i in reversed(range(len(layers))):
            body, name, over = layers[i]
            # The body with every binder outside this one already standing
            # at its witness, and then with this one too. Put in place of
            # the name where it stands rather than substituted for it: a
            # witness that is a term is not a setvar, and substituting one
            # for the other would leave the `cv` standing over a class.
            var = self.flabel[name]
            held = body
            for _b, n, _o in layers[:i]:
                held = self.restated(held, f'{self.flabel[n]} cv', stood[n])
            here = self.restated(held, f'{var} cv', stood[name])
            ph, ps = held.rpn(self.flabel), here.rpn(self.flabel)
            if proof is None:
                proof = self.settle(here, scope, facts)
                if declined(proof):
                    return proof
            witness = stood[name]
            instance = self.prove_essential(
                self.to_term(self.seq(self.seq(f'{var} cv', witness, 'wceq'),
                                 self.seq(ph, ps, 'wb'), 'wi')), scope, facts)
            if declined(instance):
                return instance
            member = self.seq(witness, over, 'wcel')
            stands = self.settle(self.to_term(member), scope, facts)
            if declined(stands):
                return stands
            proof = self.seq(scope, self.seq(member, ps, 'wa'),
                        self.seq(ph, var, over, 'wrex'),
                        self.seq(scope, member, ps, stands, proof, 'jca'),
                        ph, ps, var, witness, over, instance, 'rspcev',
                        'syl')
        return proof

    def as_generalised(self, label, goal, scope, facts, step, seed):
        """A lemma said of every such name.

        `dvdslegcd` says a common divisor is no greater than the gcd, of
        whatever divisor it is given, and `def:stdlib/divisibility/gcd` says it
        of every e in ℕ. The name is fixed, the lemma applied to it, and `ralrimiva`
        gives it back — the same move a `fix` block closes with, over a
        lemma rather than over a block.
        """
        if goal.label != 'wral':
            return Declined('the claim is not "for every"')
        body, variable, over = goal.children
        member = self.seq(f'{variable.rpn(self.flabel)} cv',
                     over.rpn(self.flabel), 'wcel')
        frame = len(self.frames)
        inner, lifted = self.widen(scope, facts, member)
        try:
            proof = self.apply_lemma(label, body, inner, lifted, step,
                                     crossing=False, seed=seed)
        finally:
            del self.frames[frame:]
        if declined(proof):
            return proof
        return self.seq(scope, body.rpn(self.flabel), variable.rpn(self.flabel),
                   over.rpn(self.flabel), proof, 'ralrimiva')

    def as_conjunct(self, label, whole, reads, goal, scope, facts, step, seed):
        """One half of what a lemma concludes.

        `gcddvds` says in one conjunction that a gcd divides both its
        arguments, and `def:stdlib/divisibility/gcd` states those as two
        sentences because a reader reads them as two. The half the claim is
        fixes the lemma, and `simpld` or `simprd` takes it.
        """
        if reads.label != 'wa' or len(reads.children) != 2:
            return Declined(f'{label} does not conclude a conjunction')
        asks, walk = [], whole
        while walk.label in ('wi', 'wb') and walk is not reads:
            asks.append(walk.children[0])
            walk = walk.children[1]
        for i, part in enumerate(reads.children):
            bound = kernel.match(part, goal, dict(seed or {}), whole.names())
            if bound is None:
                continue
            # A half need not name everything the lemma does: `ssdifsn` says
            # what is not in the subset without saying what it is a subset
            # of, and what is left open is what the step cited a line for.
            for slot in asks:
                if not reads.names() - set(bound):
                    break
                for held in facts:
                    filled = kernel.match(slot, self.to_term(held),
                                          dict(bound), whole.names())
                    if filled is not None:
                        bound = filled
                        break
            if reads.names() - set(bound):
                continue
            said = reads.substitute(bound)
            proof = self.apply_lemma(label, said, scope, facts, step,
                                     crossing=False, seed=bound)
            if declined(proof):
                continue
            a, b = (one.rpn(self.flabel) for one in said.children)
            return self.seq(scope, a, b, proof, 'simpld' if i == 0 else 'simprd')
        return Declined(f'neither half of what {label} concludes is the claim')

    def as_seeded(self, label, reads, goal, scope, facts, step, seed):
        """A lemma whose `with` target already says what it concludes.

        Where the seed fixes every variable there is nothing left for the
        claim to fix, and the two need not be spelt the same: `dvds2ln`
        writes the multiplier before the number being divided and the
        corpus writes it after, so what the lemma gives is what the step
        claims with each product exchanged. `db/notation.records` declares
        that the product may be, and `bridging` carries it.

        Only with a full seed. A claim left to fix a variable is a claim
        the conclusion has to match, or the lemma would be applied at
        whatever made the bridge work rather than at what the item says.
        """
        if seed is None or reads.names() - set(seed):
            return Declined(f'the target does not fix every variable of '
                            f'{label}')
        said = reads.substitute(seed)
        if said.rpn(self.flabel) == goal.rpn(self.flabel):
            return Declined(f'{label} at its seed is the claim as written')
        proof = self.apply_lemma(label, said, scope, facts, step,
                                 crossing=False, seed=seed)
        if declined(proof):
            return proof
        # No bridge means the lemma is not this claim said otherwise. A
        # target may name several lemmas, each giving a part of what the
        # item says, and then none of them is.
        across = self.bridging(said, goal, scope, facts, step)
        if declined(across):
            across = self.by_equation(said, goal, scope, facts, step)
        if across is None or declined(across):
            return Declined(f'nothing carries what {label} gives to the claim')
        return self.seq(scope, said.rpn(self.flabel), goal.rpn(self.flabel), proof,
                   across, 'mpbid')

    def by_equation(self, said, goal, scope, facts, step):
        """A lemma's conclusion carried to the claim by an equation proved.

        `hashun` says the size of a disjoint union is the sum of the two
        sizes; `thm:stdlib/counting/card-disjoint-union` assumes each size is
        a number and states the claim in those numbers, so what stands between the two
        is the equations the item assumes. The step cites the lines that
        prove them — `substitute` is the readable method for the same
        rewrite, and the text writes no step for it here because the item
        already said which equations are in play.

        The walk decides where to ask, so nothing is looked for: each place
        the two terms differ is one equation, and it is settled where it
        stands. A difference the scope does not prove is not a route.
        """
        def proved(one, other, where, held):
            if one.rpn(self.flabel) == other.rpn(self.flabel):
                return None
            asked = self.seq(one.rpn(self.flabel), other.rpn(self.flabel), 'wceq')
            if asked not in held:
                return None      # the walk goes on to where they differ
            return held[asked]

        straight = self.congruence(said, goal, scope, facts, step, proved)
        if not declined(straight):
            return straight
        if goal.label != 'wceq' or len(goal.children) != 2:
            return None
        # An equation is the same equation written the other way round, and
        # a lemma need not write it the way the item states it: `hashen`
        # equates the size already known with the size being asked for, and
        # the step claims the second of them. `eqcom` is closed, so it
        # crosses into the scope rather than being proved inside it.
        turned = kernel.Term('wceq', goal.children[::-1])
        across = self.congruence(said, turned, scope, facts, step, proved)
        if declined(across):
            return None
        both = [c.rpn(self.flabel) for c in turned.children]
        return self.seq(scope, said.rpn(self.flabel), turned.rpn(self.flabel),
                   goal.rpn(self.flabel), across,
                   self.seq(self.seq(turned.rpn(self.flabel), goal.rpn(self.flabel),
                           'wb'), scope, self.seq(*both, 'eqcom'), 'a1i'), 'bitrd')

    def crossed(self, label, whole, reads, goal, scope, facts, step):
        """A lemma reaching a claim set.mm says is the same claim.

        `exprmfct` says there is a prime dividing a number; the readable
        line says there is a natural number, prime, dividing it. Those are
        one statement written two ways, and `rexss` is set.mm saying so:
        quantifying over a subset is quantifying over the set with
        membership of the subset moved into the body.

        So where what a lemma concludes is not what is wanted, a declared
        biconditional is asked whether the two are the same thing. The goal
        is ground, so matching one side of the bridge against it fixes the
        bridge; the other side is then determined, and matching that against
        the lemma's conclusion fixes what the goal could not.

        The bridge comes from `rules.MEMBERSHIP` and nowhere else, which
        is the rule that stops an elaborator reaching a claim by whatever it
        can find that fits.
        """
        variables = whole.names()
        want = goal.rpn(self.flabel)
        for bridge in rules.MEMBERSHIP:
            other = self.sigs.get(bridge)
            if other is None or other.essentials:
                continue
            says = self.syntax.statement(other)
            names = says.names()
            while says.label == 'wi':
                says = says.children[1]
            if says.label != 'wb':
                continue
            for near, far in (says.children, says.children[::-1]):
                bound = kernel.match(far, goal, {}, names)
                if bound is None:
                    continue
                # A side the goal did not fix would leave the bridge's own
                # variable standing in what is proved. Asked of the side
                # rather than of the result: the proof has names of its own
                # and one of them is spelt `A`, which is also what `rexss`
                # calls the set it quantifies over.
                if near.names() - set(bound):
                    continue
                candidate = near.substitute(bound)
                if kernel.match(reads, candidate, {}, variables) is None:
                    continue
                said = candidate.rpn(self.flabel)
                found = self.apply_lemma(label, candidate, scope, facts,
                                         step, crossing=False)
                if declined(found):
                    continue
                alike = self.settle(self.to_term(self.seq(said, want, 'wb')),
                                    scope, facts)
                if declined(alike):
                    continue
                return self.seq(scope, said, want, found, alike, 'mpbid')
        return Declined(f'no declared biconditional carries what {label} '
                        f'concludes to the claim')

    def sethood(self, slot, binding):
        """The classes an antecedent asks about and nothing decides.

        `hashsng` asks `A e. V` and concludes about `{ A }`, so nothing it
        says fixes the class; `hashvnfin` asks it inside a conjunction and
        is the same. set.mm leaves such a class free so that a citation may
        name any class holding A, and what it is asking is that A be a set.
        `_V` is how that is written, and the weakest class there is to
        write, so nothing is lost by writing it.

        Read only after the conclusion and the scope have both been asked,
        so a class the step does decide is decided by the step.
        """
        out, rest = [], [slot]
        while rest:
            node = rest.pop()
            if node.label == 'wa':
                rest.extend(node.children)
                continue
            if node.label in ('wral', 'wal'):
                rest.append(node.children[0])
                continue
            # Where a map's values land is the same kind of question as where
            # a set lives, and set.mm asks it the same way: `f1f1orn` wants a
            # codomain and says nothing about it, because being one-to-one
            # into one class is being one-to-one into any that holds the
            # values. `_V` holds them all.
            at = {'wcel': 1, 'wf': 1, 'wf1': 1, 'wfo': 1, 'wf1o': 1}.get(
                node.label)
            if at is None:
                continue
            name = node.children[at].variable
            if name is not None and name not in binding:
                out.append(name)
        return out

    def apply_lemma(self, label, goal, scope, facts, step, crossing=True,
                    seed=None):
        """Apply one set.mm lemma to reach a claim, side conditions and all.

        What a lemma states before the claim it reaches may be an
        implication or a biconditional: `dvds1` says that on ℕ0, dividing
        one and being one are the same, and a step citing it has the
        dividing and wants the being. Both are peeled, and which one each
        was decides how it is discharged.

        `seed` is what a `with` target said the lemma's variables stand
        for. The match confirms it where the conclusion is the claim, and
        supplies it where the conclusion is the claim said differently and
        so fixes nothing.
        """
        sig = self.sigs[label]
        whole = self.syntax.statement(sig)
        variables = whole.names()
        # The readable "a or b or c" is built from the left, and set.mm
        # states a three-way disjunction as one constructor: `lttri4` says
        # A < B, A = B or B < A with `w3o`. `df-3or` says they are the same.
        ends = whole
        while ends.label in ('wi', 'wb'):
            ends = ends.children[1]
        if (ends.label == 'w3o' and goal.label == 'wo'
                and goal.children[0].label == 'wo'):
            three = [*(c.rpn(self.flabel) for c in goal.children[0].children),
                     goal.children[1].rpn(self.flabel)]
            said = self.seq(*three, 'w3o')
            got = self.apply_lemma(label, self.to_term(said), scope, facts,
                                   step, crossing, seed)
            if declined(got):
                return got
            return self.seq(scope, said, goal.rpn(self.flabel), got,
                            self.seq(*three, 'df-3or'), 'sylib')
        antecedents, joins, reads, binding = [], [], whole, None
        while True:
            binding = kernel.match(reads, goal, dict(seed or {}), variables)
            if binding is not None:
                break
            if reads.label not in ('wi', 'wb'):
                if crossing:
                    through = self.through_existential(
                        label, whole, reads, goal, scope, facts, step, seed)
                    if not declined(through):
                        return through
                    seeded = self.as_seeded(label, reads, goal, scope, facts,
                                            step, seed)
                    if not declined(seeded):
                        return seeded
                    part = self.as_conjunct(label, whole, reads, goal, scope,
                                            facts, step, seed)
                    if not declined(part):
                        return part
                    every = self.as_generalised(label, goal, scope, facts,
                                                step, seed)
                    if not declined(every):
                        return every
                    return self.crossed(label, whole, reads, goal, scope,
                                        facts, step)
                return Declined(f'{label} does not conclude the claim')
            # A biconditional says one thing and reaching it either way is
            # reaching it: `elnnz` says a natural number is an integer above
            # zero, and a step with the integer and the bound wants the
            # natural number, which is the side a forward read peels off.
            # Tried only where the forward read has already failed, so a
            # lemma that fits as it stands fits as it always did.
            if reads.label == 'wb':
                # With the seed, as the forward read is: `halfpos2` says
                # 0 < A exactly when 0 < A / 2, and the claim 0 < δ / 2
                # fits the near side at A := δ / 2 unless the target says A
                # is δ.
                turned = kernel.match(reads.children[0], goal,
                                      dict(seed or {}), variables)
                if turned is not None:
                    antecedents.append(reads.children[1])
                    joins.append(TURNED)
                    binding, reads = turned, reads.children[0]
                    break
                # The near side may be the claim said differently, and only
                # a full seed can tell: `hashen` equates two sizes and the
                # step claims one of them, so nothing in the goal matches
                # either side and nothing in it fixes the lemma's classes.
                if crossing:
                    seeded = self.as_seeded(label, reads.children[0], goal,
                                            scope, facts, step, seed)
                    if not declined(seeded):
                        return seeded
                # One way of the biconditional may be the claim: `suprleub`
                # says the supremum is at most B exactly when nothing in the
                # set is above B, and a least upper bound is at most every
                # such B, which is the way from the second to the first.
                if goal.label == 'wi':
                    taken = self.one_direction(label, reads, goal, variables,
                                               scope, facts, step, crossing,
                                               seed)
                    if not declined(taken):
                        return taken
            antecedents.append(reads.children[0])
            joins.append(reads.label)
            reads = reads.children[1]

        # A lemma whose hypothesis says what one of its variables is has
        # already decided it, and the match reads the claim's answer over
        # the top. Where the two disagree the claim is not what the lemma
        # concludes, so the lemma is proved at its own value instead. What
        # a naming hypothesis decides comes first, because what a relating
        # one says is said of it.
        binding = self.read_off(sig, binding, variables)
        settled = self.instanced(sig, binding)
        if any(settled[name].rpn(self.flabel) != stood.rpn(self.flabel)
               for name, stood in binding.items()):
            return self.at_its_own_value(label, sig, goal, scope, facts,
                                         step, settled)
        # Agreeing, it is also what the lemma says of the side the claim did
        # not fix, and a biconditional crossed the other way leaves that
        # side for the hypothesis to decide.
        binding = settled
        # Two letters the lemma binds and keeps apart, which the claim spells
        # alike, cannot both be the claim's: the lemma is used with one of
        # them renamed (`letters_apart`).
        kinds = {v: t for t, v in sig.floats}
        if any(kinds.get(a) == 'setvar' == kinds.get(b)
               and a in binding and b in binding
               and binding[a].rpn(self.flabel) == binding[b].rpn(self.flabel)
               for a, b in sig.disjoint):
            return self.letters_apart(label, goal, scope, facts, step,
                                      crossing, seed)
        # The scope is where a lemma's disjointness conditions can forbid it,
        # so it is chosen before anything is built. ELABORATION.md 14.
        where, frame = self.allowed(sig, binding, variables)
        if declined(where):
            # Which scope is allowed depends on what the variables stand
            # for. `ralrnmpt` forbids its own binder in the property it
            # carries, and until a cited line fixes that binder every scope
            # holding the property looks forbidden. So what the facts decide
            # is read and the question asked again — only here, because
            # binding early changes which fact answers an antecedent.
            for slot in antecedents:
                if not slot.names() - set(binding):
                    continue
                for held in facts:
                    filled = kernel.match(slot, self.to_term(held),
                                          dict(binding), variables)
                    if filled is not None:
                        binding = filled
                        break
            where, frame = self.allowed(sig, binding, variables)
            if declined(where):
                return where
        known = self.with_cited(
            step, where, self.supplied(step, where,
                                       self.frames_facts(frame, facts)))
        for slot in antecedents:
            if not slot.names() - set(binding):
                continue
            if slot.variable is not None:
                binding[slot.variable] = self.to_term(where)
                continue
            # What the lemma concludes need not fix everything it asks, so
            # an antecedent that is still open is matched against something
            # the step already has: `orel2` learns which disjunct is ruled
            # out from the line that rules it out. One that asks several
            # things at once is matched a conjunct at a time, since each is
            # a line of its own: `sstr` asks A ⊆ B and B ⊆ C, and only the
            # lines say what B is.
            for piece in self.conjuncts_of(slot):
                if not piece.names() - set(binding):
                    continue
                for held in known:
                    filled = kernel.match(piece, self.to_term(held),
                                          dict(binding), variables)
                    if filled is not None:
                        binding = filled
                        break
            for open_class in self.sethood(slot, binding):
                binding[open_class] = self.to_term('cvv')
        essentials = [self.prove_essential(
            self.syntax.parse(e[1:], 'wff').substitute(binding), where, known)
            for e in sig.essentials]
        for one in essentials:
            if declined(one):
                return one
        proof = self.ap(label, self.spelt(binding), *essentials)
        if not antecedents:
            # The lemma asks nothing, so it states the claim outright and has
            # to be brought into the scope the step sits in.
            return self.carry(self.seq(goal.rpn(self.flabel), where, proof, 'a1i'),
                              goal.rpn(self.flabel), frame)
        carried = stood_under = False
        for i, slot in enumerate(antecedents):
            asks = slot.substitute(binding)
            if asks.rpn(self.flabel) == where:
                carried = True
                # A variable slot is the context a deduction-form lemma is
                # stated in, and uses nothing; a formula the scope happens to
                # be is what the lemma asks, and uses all of it.
                stood_under = stood_under or slot.variable is None
                continue                      # the deduction slot
            rest = goal.rpn(self.flabel)
            for later, join in reversed(list(zip(antecedents[i + 1:],
                                                 joins[i + 1:], strict=True))):
                if later.substitute(binding).rpn(self.flabel) != where:
                    said = later.substitute(binding).rpn(self.flabel)
                    # A biconditional crossed the other way puts the claim
                    # on the left, where every other join puts what is asked
                    # on the left: `hashen` asks two sets be finite and then
                    # equates their sizes with a bijection, and reaching the
                    # sizes from the bijection reads it right to left.
                    rest = (self.seq(rest, said, 'wb') if join is TURNED
                            else self.seq(said, rest, join))
            # What decides the fold is whether what has been built so far
            # states its claim outright or states it under the scope. The
            # bare lemma states it outright — unless one of its own
            # antecedents was the scope, which `ssneld` does: it asks for
            # the inclusion under the scope and then says, still under it,
            # that what is outside the larger set is outside the smaller.
            first = proof.text.rsplit(None, 1)[-1] == label and not carried
            fold = {('wi', True): 'syl', ('wi', False): 'mpd',
                    ('wb', True): 'sylib', ('wb', False): 'mpbid',
                    (TURNED, True): 'sylibr', (TURNED, False): 'mpbird'}
            # `mpbird` names the two sides in the order it states them, and
            # a crossed biconditional states the claim first; every other
            # fold states what is asked first.
            sides = ((rest, asks.rpn(self.flabel))
                     if joins[i] is TURNED and not first
                     else (asks.rpn(self.flabel), rest))
            # A "there is" the lemma asks can be given by an instance a line
            # the step cites names: `suprcl` asks that S be bounded above,
            # and step 8 of the intermediate value proof cites that b is an
            # upper bound. Only then is the step passed, so every other side
            # condition is settled from declared lemmas as before.
            instanced = any(self.to_term(part).label == 'wrex'
                            for part in self.parts(asks.rpn(self.flabel)))
            under = (self.settle(asks, where, known, step=step,
                                 lines=self.lines)
                     if instanced and step is not None
                     else self.settle(asks, where, known))
            if declined(under):
                return under
            proof = self.seq(where, *sides, under, proof,
                        fold[(joins[i], first)])
        if stood_under:
            # An antecedent that is the scope is supplied by standing under
            # it, not by a fact looked up, so what it rests on is not carried
            # in by one: `readdcl` asks `( A ∈ ℝ ∧ B ∈ ℝ )`, the triangle
            # inequality's scope is exactly that, and its step 1 is the
            # lemma alone. It rests on everything the scope says.
            proof = Proof(proof.text,
                          proof.origin | self.scope_origin(where, known))
        return self.carry(proof, goal.rpn(self.flabel), frame)

    def at_its_own_value(self, label, sig, goal, scope, facts, step, settled):
        """A lemma proved at the value its own hypothesis gives it.

        `fsum1` concludes that a one-term sum is B and asks `( k = M -> A
        = B )`, which is not a condition on B but a statement of what B
        is. Taking B from the claim instead makes the hypothesis say
        something the claim's own words cannot prove: `G(0) = 1` asks that
        `a^k` be 1 at k = 0, which is `exp0` and wants a complex a, and a
        hypothesis with no antecedent has nothing to say about a.

        So the lemma proves what it does say — `G(0) = a^0` — and the
        claim is settled from that, here, where the theorem's `let a ∈ ℝ`
        is in scope. That is the only place the fact is available and the
        reason the closed hypothesis could never have carried it.
        """
        reads = self.syntax.statement(sig)
        while reads.label == 'wi':
            reads = reads.children[1]
        said = reads.substitute(settled)
        # Not a way back here: the match against `said` gives `settled`
        # back, and reading a hypothesis twice reads the same value.
        proof = self.apply_lemma(label, said, scope, facts, step,
                                 crossing=False)
        if declined(proof):
            return proof
        known = dict(facts)
        known[said.rpn(self.flabel)] = proof
        return self.settle(goal, scope, known)

    def prove_essential(self, want, scope, facts):
        """One hypothesis a lemma states in full rather than asking for."""
        if (want.label == 'wceq' and len(want.children) == 2
                and want.children[0].rpn(self.flabel)
                == want.children[1].rpn(self.flabel)):
            # A lemma that names a thing so that its conclusion may speak of
            # it asks for the naming, and asks for it as it stands rather
            # than under the scope: `ralrnmpt` wants `F = ( x e. A |-> B )`
            # of the very map F is. `settle` would carry it into the scope,
            # which is a deduction where the hypothesis is a statement.
            return self.seq(want.children[0].rpn(self.flabel), 'eqid')
        if want.label != 'wi':
            return self.settle(want, scope, facts)
        left, right = want.children
        under = left.rpn(self.flabel)
        if under == right.rpn(self.flabel):
            return self.seq(under, 'id')
        # A lemma may state its instance rather than ask for it: `elrab`
        # says what belongs to a set-builder by way of the body read at the
        # element, and wants the body before and after tied together.
        # `fsum1` does it with two terms where `elrab` does it with two
        # formulas, and the walk between them is the same walk.
        if (left.label == 'wceq' and right.label in ('wb', 'wceq')
                and left.children[0].label == 'cv'):
            was = left.children[0].rpn(self.flabel)
            now = left.children[1].rpn(self.flabel)

            # The equation is what is assumed, so it is handed over as a
            # fact rather than reproved at the leaf: the walk widens the
            # scope where it passes a binder, and a proof under the scope
            # it started at would not be a proof under that one.
            def stands(one, other, _where, held):
                return (held.get(under)
                        if one.rpn(self.flabel) == was
                        and other.rpn(self.flabel) == now else None)
            return self.congruence(right.children[0], right.children[1],
                                   under, {under: self.seq(under, 'id')}, None,
                                   stands)
        if under == scope:
            return self.settle(right, scope, facts)
        if (left.label == 'wa'
                and left.children[0].rpn(self.flabel) == scope):
            extra = left.children[1].rpn(self.flabel)
            wider = {k: self.seq(under, scope, k, self.seq(scope, extra, 'simpl'), v,
                            'syl') for k, v in facts.items()}
            wider[extra] = self.seq(scope, extra, 'simpr')
            taken = self.at_the_index(left.children[1], right, under, wider)
            if taken is not None:
                return taken
            # One level deeper than `settle`'s default: what is asked of an
            # index is asked through the range it runs over, and the index
            # is in ℕ₀ only by `elfznn0` from that. `fsumdvds` asks the
            # digit sum's term d(k)·10^k − d(k) to be an integer, which is
            # `zsubcl`, `zmulcl`, `ffvelcdm` and then `elfznn0`.
            return self.settle(right, under, wider, depth=4)
        return self.settle(right, under, {})

    @staticmethod
    def conjuncts_of(slot):
        """The things a lemma's antecedent asks, one conjunct at a time."""
        pieces, parts = [], [slot]
        while parts:
            part = parts.pop(0)
            if part.label in ('wa', 'w3a'):
                parts[:0] = part.children
            else:
                pieces.append(part)
        return pieces

    def at_the_index(self, member, right, under, facts):
        """What a lemma asks of each index, from a line saying it of all.

        `fsumdvds` asks, for k in the range it sums over, that N divide the
        term, and the divisibility proof says it for every k ∈ ℕ₀. That is
        the line read at k, once k is in ℕ₀, which `rspcv` does. The line
        binds a letter of its own, since its `fix` introduced the index
        before the sum bound one, so what is compared is its body read at
        k. Only a line in hand whose body at k is what is asked is read so,
        which makes this an instantiation and not a search.

        None where no such line is in hand, which is not a decline: the
        caller settles what is asked another way.
        """
        if member.label != 'wcel' or member.children[0].label != 'cv':
            return None
        index = member.children[0]
        want = right.rpn(self.flabel)
        # Only what the step names, as `settle` is offered only that: a
        # line in scope and not cited is not there to be read.
        if self.resting is not None:
            facts = {k: v for k, v in facts.items()
                     if getattr(v, 'origin', frozenset()) <= self.resting}
        for said, proof in facts.items():
            line = self.to_term(said)
            if line.label != 'wral' or line.children[1].variable is None:
                continue
            body, letter, over = line.children
            if body.substitute({letter.variable: index.children[0]}).rpn(
                    self.flabel) != want:
                continue
            inside = self.seq(index.rpn(self.flabel), over.rpn(self.flabel),
                              'wcel')
            there = self.settle(self.to_term(inside), under, facts)
            if declined(there):
                continue
            reads = self.to_term(self.seq(
                self.seq(f'{letter.rpn(self.flabel)} cv',
                         index.rpn(self.flabel), 'wceq'),
                self.seq(body.rpn(self.flabel), want, 'wb'), 'wi'))
            tied = self.prove_essential(reads, under, facts)
            if declined(tied):
                continue
            read = self.ap('rspcv', {'ph': body.rpn(self.flabel), 'ps': want,
                                     'x': letter.rpn(self.flabel),
                                     'A': index.rpn(self.flabel),
                                     'B': over.rpn(self.flabel)}, tied)
            carried = self.seq(under, inside, self.seq(said, want, 'wi'),
                               there, read, 'syl')
            return self.seq(under, said, want, proof, carried, 'mpd')
        return None

    def one_direction(self, label, reads, goal, variables, scope, facts,
                      step, crossing, seed):
        """A claim `P → Q` from a lemma saying `Q ↔ P`, or `P ↔ Q`.

        The biconditional is proved at what the claim fixes, as the lemma
        states it, and the way the claim goes is taken: `biimpd` from left
        to right, `biimprd` from right to left.
        """
        left, right = reads.children
        for (first, then), fold in (((left, right), 'biimpd'),
                                    ((right, left), 'biimprd')):
            fixed = kernel.match(kernel.Term('wi', (first, then)), goal,
                                 dict(seed or {}), variables)
            if fixed is None:
                continue
            said = reads.substitute(fixed)
            both = self.apply_lemma(label, said, scope, facts, step,
                                    crossing, fixed)
            if declined(both):
                return both
            return self.seq(scope, left.substitute(fixed).rpn(self.flabel),
                            right.substitute(fixed).rpn(self.flabel), both,
                            fold)
        return Declined(f'neither way of {label} is the claim')

    def fresh(self, prefix):
        """A label for a generated statement nothing else is using.

        `ine1` reads as the first inequality assumed; set.mm reads it as
        `_i =/= 1`, and a file that includes another numbers its own from one
        as well. So the label says which file it belongs to, and is looked
        for rather than taken: the library is large enough that a short name
        is never safely free.
        """
        stem = label_of(qualified(self.thm), self.sigs, self.thm.path,
                        self.thm.line, proved_here(self.items))
        number = len(self.axioms) + 1
        while f'{stem}.{prefix}{number}' in self.sigs:
            number += 1
        return f'{stem}.{prefix}{number}'

    @staticmethod
    def outermost(words, relation):
        """Where a chain's first line puts its relation: the first time the
        symbol stands outside every bracket.

        A sum binds its index with the same `=` a chain relates by, so
        `x·(Σ(k = 0 to m) t(k)) = …` has an `=` inside the sum before the
        one the chain means.
        """
        depth = 0
        for at, word in enumerate(words):
            if depth == 0 and word == relation:
                return at
            depth += sum(word.count(c) for c in '({[') \
                - sum(word.count(c) for c in ')}]')
        return words.index(relation)

    def calculation(self, step, node, term, scope, facts, lines):
        """A chain folded by transitivity, one link at a time.

        A link carries a relation of its own, and they need not all be the
        same: the triangle inequality runs two equalities into a `≤`. So each
        link is read as the claim relating the run so far to what the link
        adds, and the lemma that folds it is chosen by the two relations
        either side of the join.

        A link may cite a line the other way round — `3.3, right to left` —
        because nothing in the readable layer says which way an equation
        faces, and the chain wants them all facing the same way.
        """
        links = []
        for text, _line in step.just.chain:
            turned = 'right to left' in text
            body = re.sub(r',\s*right to left\s*$', '', text).strip()
            body, cite = body.rsplit(None, 1)
            links.append((body.strip(), cite, turned))

        def held(cite, turned, claim, written):
            # A link of numerals alone may name `arithmetic` rather than a
            # line, and what it relates is proved where it stands.
            if cite == 'arithmetic':
                return self.closed_fact(
                    claim.rpn(self.flabel), scope, facts,
                    f'a link of step {fmt(step.number)} claims {written}',
                    step)
            line = lines[cite]
            proof = self.carried(cite, facts, lines)
            if not turned:
                return proof
            was, now = (c.rpn(self.flabel)
                        for c in self.to_term(line.term).children)
            return self.seq(scope, was, now, proof, 'eqcomd')

        first = self.read(links[0][0])
        if not first.text:
            raise self.defect(step.line, 'a chain starts with no relation')
        words = links[0][0].split()
        rest = ' '.join(words[self.outermost(words, first.text) + 1:])
        whole = self.to_term(self.term(first))
        left = whole.children[0].rpn(self.flabel)
        right = whole.children[1].rpn(self.flabel)
        said = whole.label
        relation = whole.children[2].rpn(self.flabel) if said == 'wbr' else ''
        proof = held(links[0][1], links[0][2], whole, links[0][0])
        for body, cite, turned in links[1:]:
            mark, added = body.split(None, 1)
            joined = self.to_term(self.term(self.read(f'{rest} {mark} {added}')))
            fold = rules.FOLDING.get((said, joined.label))
            if fold is None:
                raise self.defect(step.line,
                                  f'no transitivity folds {said} into '
                                  f'{joined.label}')
            if joined.children[0].rpn(self.flabel) != right:
                raise self.defect(step.line,
                                  'a link that reads the other way round '
                                  'from the one above it')
            nxt = joined.children[1].rpn(self.flabel)
            if joined.label == 'wbr':
                relation = joined.children[2].rpn(self.flabel)
            proof = self.seq(scope, left, right, nxt, relation, proof,
                        held(cite, turned, joined,
                             f'{rest} {mark} {added}'), fold)
            right, rest = nxt, added
            said = 'wceq' if said == joined.label == 'wceq' else 'wbr'
        return proof

    def exhibit(self, step, node, term, scope, facts, lines):
        """An existence claim shown by naming something that answers it.

        The witness is not written. It is read off a line the step cites, by
        walking that line against the shape the claim quantifies: step 3.16
        claims something above 1 divides both, and the line saying 2 divides
        p is what says the something is 2. That is the same expansion as a
        definition used to conclude an existence claim, with the witness
        coming from a different place. `ELABORATION.md` requirement 7.
        """
        whole = self.to_term(term)
        if whole.label != 'wrex':
            raise self.defect(step.line,
                              'an exhibit that claims no existence')
        # A claim may quantify over more than one name — Bezout exhibits an
        # x and a y together — and reading several witnesses off the lines a
        # step cites is what `witnessed` does, innermost first.
        if whole.children[0].label == 'wrex':
            return self.witnessed(step, whole, scope,
                                  self.supplied(step, scope, facts), lines)
        body, _variable, domain = whole.children
        # The name the text quantifies under and the variable it stands for
        # are two different things: Cantor quantifies over B, which set.mm
        # declares as a class, so the claim binds a setvar of its own.
        said = node.children[0].text
        stands = f'{self.binder_var(said)} cv'
        witness = None
        for ref in step.just.refs:
            witness = self.witness_in(body, self.to_term(lines[ref].term),
                                      stands)
            if witness:
                break
        if witness is None:
            raise self.defect(step.line, 'no cited line names a witness')

        saved = dict(self.names)
        self.names[said] = stands
        shape = self.freeze(node.children[2])
        self.names = saved
        at = self.seq(stands, witness, 'wceq')
        made = self.rewrite(shape, stands, witness, at, self.seq(at, 'id'))
        if declined(made):
            raise self.defect(step.line,
                              f'the witness stands nowhere in the claim: '
                              f'{made}')
        here, instance = made

        known = self.supplied(step, scope, facts)
        member = self.seq(witness, domain.rpn(self.flabel), 'wcel')
        # An `exhibit` is the head of a step. The witness is read off the
        # lines it cites, so what is left is that the witness lies in the
        # domain and that the body holds of it, and both are the text's to
        # supply rather than another route's to try.
        shown = []
        for want in (member, here):
            one = self.settle(self.to_term(want), scope, known)
            if declined(one):
                raise self.defect(
                    step.line,
                    f'exhibiting that witness wants {self.render(want)}, '
                    f'which step {fmt(step.number)} does not supply: {one}')
            shown.append(one)
        spare = self.binder_var(said)
        return self.seq(scope, self.seq(member, here, 'wa'), term,
                   self.seq(scope, member, here, *shown, 'jca'),
                   body.rpn(self.flabel), here, spare,
                   witness, domain.rpn(self.flabel), instance, 'rspcev',
                   'syl')

    def witness_in(self, pattern, actual, mark):
        """What stands where `mark` does, in a line shaped like the pattern."""
        found = self.witnesses_in(pattern, actual, {mark})
        return found[mark] if found else None

    def witnesses_in(self, pattern, actual, marks):
        """What stands where each of `marks` does, or nothing unless all do.

        A cited line answers part of a claim rather than all of it — 3.14
        says 2 divides p, which is one of the three things 3.16 asks of d —
        so the search runs over the claim's parts, aligning each against the
        whole of the line. Alignment starts only at a part built the same
        way the line is, or the bare `d` inside a part would align with the
        line entire and the witness would come out as the line.

        Several marks at once is what a nested existential asks for. The
        Bezout proof cites `a = a·1 + b·0` for a body quantified over two
        names, and looking for one of them at a time finds neither: where
        the pattern holds the other's variable the line holds a numeral, and
        a place that has to agree does not.
        """
        found = {}
        if (pattern.label == actual.label
                and self.aligned(pattern, actual, marks, found)
                and len(found) == len(marks)):
            return found
        for child in pattern.children:
            got = self.witnesses_in(child, actual, marks)
            if got:
                return got
        return None

    def aligned(self, pattern, actual, marks, found, paired=None):
        """Whether these agree everywhere but the marked places.

        A letter each binds at the same place may differ, and is the same
        letter below it: `suprcl` asks that some x bound every y in S, and
        the line saying b is an upper bound of S says it of every s. A
        letter neither binds there must be the same letter.
        """
        paired = paired or {}
        here = pattern.rpn(self.flabel)
        if here in marks:
            was = actual.rpn(self.flabel)
            return found.setdefault(here, was) == was
        if pattern.variable is not None or actual.variable is not None:
            return paired.get(pattern.variable,
                              pattern.variable) == actual.variable
        if pattern.label != actual.label:
            return False
        if len(pattern.children) != len(actual.children):
            return False
        if (pattern.label in rules.BOUND and len(pattern.children) >= 2
                and pattern.children[1].variable is not None
                and actual.children[1].variable is not None):
            paired = {**paired, pattern.children[1].variable:
                      actual.children[1].variable}
        return all(self.aligned(a, b, marks, found, paired)
                   for a, b in zip(pattern.children, actual.children,
                                   strict=True))

    def conclude(self, step, node, term, scope, facts, lines):
        """A definition used the other way: to conclude an existence claim.

        The witness is never written in the text. It is read off the cited
        line, by walking the shape the definition states against it.
        """
        subject = self.term(self.read(instantiation(step.just.text)[0][1]))
        var = self.spare_var()
        saved = dict(self.names)
        # A definition may name more than the thing it is about:
        # `def:stdlib/divisibility/divides` is about d and says what it
        # divides, and the step fills in both.
        for name, value in instantiation(step.just.text):
            self.names[name] = self.term(self.read(value))
        lemma, var, kernel, _w, over, _left = self.definition(
            step.just.head, subject, var=var)
        kernel = self.freeze(kernel)
        self.names = saved

        # A step cites the lines it leans on, and only one of them says what
        # the witness is: 3.14 cites 3.1 for p being an integer and 3.6 for
        # p being twice something. The line taken is the one whose claim is
        # what the definition would say of the witness it names, which the
        # text may write facing either way.
        body = self.term(kernel)
        mark = f'{var} cv'
        # A requires line may say it too, where what names the witness is a
        # fact of numerals alone: `requires 9 = 3·3: arithmetic` under
        # `3 divides 9`. The cited lines are asked first, as before.
        candidates = [(lines[ref].term,
                       lambda ref=ref: facts.get(lines[ref].term,
                                                 lines[ref].proof))
                      for ref in step.just.refs]
        if step.requires:
            known = self.supplied(step, scope, facts)
            for text, _how, _no in step.requires:
                said = self.claim_of(text)
                if said in known:
                    candidates.append((said, lambda said=said: known[said]))
        for said, proof_of in candidates:
            held = self.to_term(said)
            witness = None
            for shape in (body, self.turned(body)):
                if shape is not None:
                    witness = self.witness_in(self.to_term(shape), held, mark)
                if witness:
                    break
            if witness is None:
                continue
            here = self.term(self.substituted(kernel, mark, witness))
            if said in (here, self.turned(here)):
                chosen = proof_of
                break
        else:
            raise self.defect(step.line, 'no cited line names a witness')
        at = self.seq(f'{var} cv', witness, 'wceq')
        made = self.rewrite(kernel, f'{var} cv', witness, at,
                            self.seq(at, 'id'))
        if declined(made):
            raise self.defect(step.line,
                              f'the witness stands nowhere in the claim: '
                              f'{made}')
        _built, instance = made

        ex = self.seq(body, var, over, 'wrex')
        member = self.seq(witness, over, 'wcel')
        p_member = self.required(step, member, over, scope, facts)
        # The cited line faces the way the text writes the definition, and
        # the existential faces the way the lemma writes it.
        # A line proved before a block opened holds inside it too, and the
        # scope's own copy is what says so where the step sits.
        p_cited = chosen()
        if said != here:
            was = self.to_term(said)
            p_cited = self.seq(scope, *(c.rpn(self.flabel) for c in was.children),
                          p_cited, 'eqcomd')
        p_ex = self.seq(scope, self.seq(member, here, 'wa'), ex,
                   self.seq(scope, member, here, p_member, p_cited, 'jca'),
                   body, here, var, witness, over, instance, 'rspcev', 'syl')

        made = self.unfolding(step, lemma, term, ex, var, over, scope, facts)
        if declined(made):
            return made
        return self.seq(scope, term, ex, p_ex, made[0], 'mpbird')

    def cite(self, step, node, term, scope, facts, lines):
        """A theorem cited. Either set.mm supplies it or this corpus does."""
        item = self.item_cited(step.just.head)
        if proved(item):
            return self.cite_corpus(step, term, scope, facts, lines, item)
        return self.cite_library(step, term, scope, facts, lines, item)

    def cite_library(self, step, term, scope, facts, lines, item):
        """Apply the set.mm theorem the item's `target` names.

        The lemma is stated in its own variables and the item in the readable
        ones, and reading the lemma's statement is what relates them: its
        conclusion is matched against what the step claims, and what that
        leaves open is fixed by matching an antecedent against a line the
        step already has.

        That works while the conclusion is the claim. Where it is the claim
        said differently, nothing fixes the lemma's variables at all, and
        the item says which is which: `target <label> with N := n` is the
        `with` form `targets.lemma` has always read.
        """
        labels = targets.clauses(item)
        if not labels:
            # Nothing in the library has its shape, so the file states what
            # it claims and lists it, the same as an item obtained from.
            # `thm:proof/sqrt2-irrational/lowest-terms` is the case, and
            # `thm:stdlib/geometry/angle-symmetric`.
            return self.assume_item(step, term, scope, facts, item)
        seed = self.filling(step, item)
        found = self.by_clause(labels, term, scope, facts, step, seed)
        if declined(found):
            raise self.defect(step.line,
                              f'no clause of {step.just.head} reaches what '
                              f'step {fmt(step.number)} claims')
        return found

    def by_clause(self, labels, term, scope, facts, step, seed):
        """What one clause of an item gives, or what several give together.

        An item may state several things and set.mm prove each separately,
        which is why a target names one lemma per `then` group. A step
        usually claims one of them — `def:stdlib/numbers/sqrt` is cited three
        times over — but it may claim what the item says entire, as Bezout's step 15
        says what a gcd is in four sentences, and then the clauses are
        taken one to a sentence and joined.
        """
        for label in labels:
            found = self.apply_lemma(label, self.to_term(term), scope,
                                     facts, step, seed=seed)
            if not declined(found):
                return found      # otherwise not this `then` group
        node = self.to_term(term)
        if node.label != 'wa':
            return Declined('no clause of the item reaches the claim')
        halves = [self.by_clause(labels, one.rpn(self.flabel), scope, facts,
                                 step, seed) for one in node.children]
        for one in halves:
            if declined(one):
                return one
        return self.seq(scope, *(one.rpn(self.flabel) for one in node.children),
                   *halves, 'jca')

    def filling(self, step, item, cites=None):
        """What a `with` target says the lemma's variables stand for.

        The right sides are formulas in the item's own names, and the step
        wrote what those stand for, so they are read under the citation's
        instantiation — the reading `assume_item` makes of the same text,
        and from the same place, since an `obtain` writes it apart from the
        justification the step carries.
        """
        _label, fills = targets.lemma(item)
        if not fills:
            return {}
        saved = dict(self.names)
        for name, value in instantiation(cites or step.just.text):
            self.names[name] = self.term(self.read(value))
        out = {name: self.to_term(self.term(self.read(formula)))
               for name, formula in fills.items()}
        self.names = saved
        return out

    def cited_floats(self, said, classes):
        """The variables the file this corpus wrote for a theorem declares.

        Metamath asks a citation to push a term for every variable of the
        statement it applies, in the order set.mm declares those variables.
        The file gave each `let` line a class of its own and each name a
        hypothesis binds whatever setvar that name takes —
        `least-combination-divides` has eight lets and an H11 binding an x
        and a y, so its label takes ten. A citation names only what the
        citing proof calls something else, so it is no list to push.

        The binders are read off the statement as this proof has it: a name
        a hypothesis binds takes the same variable in either proof, since
        that is what `binder_var` is for. What a class variable stands for
        does not, which is why a setvar standing in for one — Bezout puts
        an obtained d where this theorem writes D — is not one of these.
        """
        bound, rest = set(), [self.to_term(one) for one in said]
        while rest:
            node = rest.pop()
            if node.label in ('wral', 'wrex', 'wreu'):
                bound.add(node.children[1].rpn(self.flabel))
            # A map written on the spot binds a name too, and it is the one
            # a set-image is the range of. `powerset-split-disjoint` states
            # its claim about such a range, so the name is in what a
            # citation has to push.
            if node.label in ('cmpt', 'wal'):
                at = 0 if node.label == 'cmpt' else 1
                bound.add(node.children[at].rpn(self.flabel))
            # and so does a sum, its index: `binomial-step` states one sum
            # over k equal to another.
            if node.label == 'csu':
                bound.add(node.children[2].rpn(self.flabel))
            rest.extend(node.children)
        return sorted(bound | set(classes),
                      key=lambda label: self.forder[label])

    def cited_pushes(self, name, binds, mine):
        """What a citation pushes, in the order the cited file declares.

        Metamath asks for a term per variable of the statement applied, in
        that file's declaration order, and two proofs need not spell a
        statement's bound names alike: the letter a set-image binds is a
        class letter, so neither proof can take it and each falls back on
        whichever spare was free. So the cited statement is read, and what
        it binds decides both the order and how many.

        The classes need no reading. Both files name a theorem's class
        hypotheses from one list in the order the theorem writes them, so
        a class stands for the same hypothesis on both sides.

        None where the file is not there, which is every proof cited before
        it has been built. Those are the ones whose names happen to agree,
        and they are pushed as they were before this.
        """
        path = path_of(name)
        if not path.exists():
            return None
        said = None
        with path.open() as handle:
            for line in handle:
                if ' $p ' in line:
                    said = line.split(' $p ')[1].split('$=')[0].split()
                    break
        if said is None:
            return None
        theirs = []
        for token in said:
            label = self.flabel.get(token)
            if label is not None and label not in theirs:
                theirs.append(label)
        theirs.sort(key=lambda label: self.forder[label])
        spare = [v for v in mine
                 if v not in binds and self.sigs[v].statement[0] == 'setvar']
        out = []
        for label in theirs:
            if label in binds:
                out.append(binds[label])
            elif self.sigs[label].statement[0] == 'setvar' and spare:
                out.append(spare.pop(0))
            else:
                return None
        return out

    def cite_corpus(self, step, term, scope, facts, lines, item, cites=None):
        """Apply a theorem this corpus proves, as this elaborator states it.

        Its hypotheses became the antecedent of one implication, so citing it
        is conjoining the facts the step supplies and applying one label.
        """
        other, full = item, qualified(item)
        if full not in self.cited:
            self.cited.append(full)
        saved, kept = dict(self.names), dict(self.sets)
        spare = list(CLASS_NAMES)
        written = dict(instantiation(cites or step.just.text))
        binds = {}
        for kind, htext, _label, _line in other.hypotheses:
            node = self.read(hypothesis_body(kind, htext))
            # `let X be a set` names a class as surely as `let n ∈ ℕ` does;
            # `hypothesis_body` has already turned it into the formula that
            # says so, and the name is in the same place. `let a ∉ X` reads
            # as a conjunction whose first leaf is the name.
            if kind == 'let' and node.notation in ('membership', 'is-a-set',
                                                   'conjunction'):
                name = self.subject_of(node).text
                theirs = spare.pop(0)
                # A hypothesis the citation does not name stands for what
                # the citing proof calls by the same word. Bezout cites this
                # theorem as `c := a` and says nothing of a, b, d, x₀ or y₀,
                # because it holds names spelt that way and those are the
                # ones it means. A word it does not hold takes a spare.
                if name in written:
                    self.names[name] = self.term(self.read(written[name]))
                elif name not in saved:
                    self.names[name] = theirs
                binds[theirs] = self.names[name]
        wanted = [self.term(self.read(hypothesis_body(kind, htext)))
                  for kind, htext, _l, _n in other.hypotheses]
        # The step may claim one sentence of a conclusion that says several:
        # `thm:proof/triangle-inequality/abs-bounds` concludes x ≤ |x| and
        # −x ≤ |x|, and a step that needs only the first says only the
        # first. The theorem gives the whole, read in its own sorts, and the
        # sentence is taken out of it.
        whole = term
        if (len(self.sentences(other.conclusion))
                > len(self.sentences(' '.join(step.claim)))):
            with self.in_its_names(other):
                whole = self.claim_of(other.conclusion)
        self.names, self.sets = saved, kept

        # A cited theorem asks for what it asks for, and a hypothesis a
        # reader would not think to write as a line is written as a
        # `requires` instead: Bezout cites this one at u := 1 and says
        # `requires 1 ∈ ℤ` rather than proving it as a step.
        known = self.supplied(step, scope, facts)
        for one in wanted:
            if one in known:
                continue
            # A hypothesis a reader would not think to write as a line and
            # would not think to write as a `requires` either: that a name
            # the proof obtained is a set. It is a side condition like any
            # other, so it is settled like one before this gives up.
            known[one] = self.settle(self.to_term(one), scope, known)
            if declined(known[one]):
                raise self.defect(step.line,
                                  f'nothing supplies {self.render(one)}, '
                                  f'which {step.just.head} assumes')
        pair, proof = wanted[0], known[wanted[0]]
        for extra in wanted[1:]:
            proof = self.seq(scope, pair, extra, proof, known[extra], 'jca')
            pair = self.seq(pair, extra, 'wa')
        # A variable the file declares and this proof says nothing about is
        # one the statement binds, and it stands for itself.
        mine = self.cited_floats([*wanted, whole], binds)
        pushed = (self.cited_pushes(full, binds, mine)
                  or [binds.get(label, label) for label in mine])
        cited = label_of(full, self.sigs, self.thm.path, self.thm.line,
                         proved_here(self.items))
        # The cited theorem is proved in another file and this one includes
        # it, so the library does not hold it and anything reading the proof
        # back cannot tell how much it takes. What it takes is what is being
        # pushed, and that is known right here. Kept apart from `self.sigs`,
        # which `label_of` reads to move off a name already in use: putting
        # it there would make the second citation of a theorem disagree
        # with the first about what the theorem is called.
        self.arities.setdefault(cited, Signature(
            cited, '$p', ['|-'],
            [('class', f'{cited}.{n}') for n in range(len(pushed))]))
        proof = self.seq(scope, pair, whole, proof, *pushed, cited, 'syl')
        if term == whole:
            return proof
        parts = {}
        self.unpack(whole, proof, scope, parts)
        if term not in parts:
            raise self.defect(step.line, f'{step.just.head} does not conclude '
                                         f'what step {fmt(step.number)} '
                                         f'claims')
        return parts[term]


def definitions(records, sigs):
    """Write the constants this corpus introduces, and what they stand for.

    A definition that names a word for something the library already has
    points at its label; one that introduces a symbol has nothing to point
    at, and the corpus has to declare the constant itself. set.mm writes the
    angle function inline in every theorem about it and never names it,
    which is the only such case the corpus has.

    They are written once, for the corpus rather than for a proof. Two
    proofs both using angles would otherwise each declare the constant, and
    the declarations would collide the moment one included the other.

    What `check.py` cannot check without the library is checked here: that
    the token is not already a label, and that the term parses and closes
    over its own variables. A definition introducing a symbol the library
    already has would not be a definition, and one whose term had a free
    variable would not be eliminable.
    """
    labels = {s.statement[1]: s.label for s in sigs.values()
              if s.kind == '$f'}
    said = []
    for r in records:
        token = r.fields.get('symbol', '').strip()
        if r.kind != 'definition' or not token:
            continue
        if f'c{token}' in sigs or token in sigs:
            raise Problem(r.path, r.line,
                          f'definition {r.name}: the library already has '
                          f'{token!r}, so this defines nothing')
        body = ' '.join(r.fields.get('defines', '').split())
        term = term_of(body, sigs)
        free = {v for v in term.names()
                if sigs[labels[v]].statement[0] != 'setvar'}
        if free:
            raise Problem(r.path, r.line,
                          f'definition {r.name}: {sorted(free)} are free in '
                          f'what it defines, so it is not eliminable')
        said.append((token, r.name, body))
    return said


def say_library(path, count):
    """Which set.mm the file being written was checked against.

    An elaborated file is a record rather than a build product: it cannot be
    rebuilt from this repository, because set.mm is 51 MB and belongs to
    metamath. So it has to say which set.mm, and set.mm carries no version of
    its own — its header gives the date the database was created in 1992 and
    nothing about the copy in hand. It is named by what it holds instead.

    The count is the half a person can use, and says at a glance whether the
    library grew. The hash is the half that decides. Both are read off the
    file and never off the clock, so elaborating twice from one library gives
    one file, and byte-identical output stays the tripwire for a change
    nobody meant to make.

    SHA-256 rather than SHA-1 because everything these proofs claim rests on
    the library being what it says it is, and chosen-prefix collisions
    against SHA-1 are practical, so a stamp that could be forged would
    certify a lie.

    `count` is read off the library before anything is elaborated. An
    elaborator adds to its own table as it goes — the corpus's definitions,
    and a label for each statement a file assumes — so counting at the point
    the header is written would count those too.
    """
    digest = hashlib.sha256(Path(path).read_bytes()).hexdigest()
    print(f'   Checked against a set.mm of {count:,} assertions, sha256')
    print(f'   {digest}. $)')


def write_definitions(records, sigs, setmm):
    """The corpus's definitions, as a file the proofs include."""
    said = definitions(records, sigs)
    print(f'$( {STDLIB}/definitions, from the {STDLIB}/*.records files by '
          f'parley/elaborate.py.')
    if said:
        print('   Each introduces one constant the library does not have,')
        print('   and stands for a term that closes over its own names.')
    else:
        print('   The corpus introduces none.')
    say_library(setmm, len(sigs))
    print()
    print('$[ set.mm $]')
    print()
    # A new symbol is declared before it is used, the way set.mm declares
    # every one of its own. Without the `$c` the syntax axiom below names a
    # token the file has never heard of.
    for token, _name, _body in said:
        print(f'$c {token} $.')
    if said:
        print()
    for token, name, body in said:
        print(f'$( {name} $)')
        print(f'  c{token} $a class {token} $.')
        print(f'  df-{token} $a |- {token} = {render(body, sigs)} $.')
    return 0


def term_of(rpn, sigs):
    """The tree a run of reverse Polish builds."""
    stack = []
    for token in rpn.split():
        sig = sigs[token]
        if sig.kind == '$f':
            stack.append(kernel.Term(variable=sig.statement[1]))
            continue
        count = len(sig.floats)
        args = stack[len(stack) - count:] if count else []
        del stack[len(stack) - count:]
        stack.append(kernel.Term(token, tuple(args)))
    return stack[0]


def main(argv, root=None):
    """Elaborate one theorem of the corpus at `root`, which is this one
    unless a caller says otherwise. `parley/test_elaborate.py` says
    otherwise, because it plants a defect in a copy.
    """
    if len(argv) < 3:
        print(__doc__.strip().splitlines()[-1], file=sys.stderr)
        return 2
    wanted, setmm = argv[1], argv[2]
    root = root or Path(__file__).resolve().parent.parent
    records, theorems = corpus(root)
    if wanted == '--definitions':
        return write_definitions(records, read_library(setmm), setmm)
    grammar = Grammar.load(records)
    items = full_names(records, theorems)
    found = [t for t in theorems if qualified(t) == wanted]
    if not found:
        print(f'no theorem {wanted!r}', file=sys.stderr)
        return 2
    thm = found[0]
    sorts_in_scope(thm, grammar)
    # What this corpus proves below the readable layer is read alongside the
    # library, so a `target` may name one of its labels exactly as it names
    # a set.mm label. The file is generated, and a proof that cites nothing
    # in it elaborates whether or not it has been built.
    supplied = path_of(GEOMETRY)
    provided = set(read_library(supplied)) if supplied.exists() else set()
    sigs = (read_library(setmm, supplied) if supplied.exists()
            else read_library(setmm))
    # Read before anything is added to the table, so it counts the library
    # and not this corpus. `say_library` says why it is recorded at all.
    library_size = len(sigs) - len(provided)
    # The constants the corpus introduces are not in the library, so a
    # notation that reaches one needs them declared before it is read. They
    # are the same statements `--definitions` writes into the file the proof
    # includes, built here rather than read back from it.
    for token, _name, body in definitions(records, sigs):
        sigs[f'c{token}'] = Signature(f'c{token}', '$a', ('class', token))
        sigs[f'df-{token}'] = Signature(
            f'df-{token}', '$a',
            ('|-', token, '=', *render(body, sigs).split()))

    work = Elaborator(thm, grammar, items, sigs, records)
    goal, hypotheses, proof = work.run()
    antecedent = hypotheses[0] if hypotheses else None
    for extra in hypotheses[1:]:
        antecedent = seq(antecedent, extra, 'wa')
    if antecedent is None:
        # Nothing is assumed, so the scope that carried the proof was truth
        # and the statement says only what the theorem concludes.
        proof = work.seq(goal, proof, 'mptru')
    # What is written out is the proof's text, and this is where it stops
    # carrying what it rests on: everything that asked has asked. It is read
    # into its shapes once, and which labels it uses is read off those: the
    # text runs to sixty-three million tokens for the intermediate value
    # theorem, and splitting it for each question held gigabytes.
    root, kinds = shapes(proof.text, {**sigs, **work.arities})
    used = compress_labels(kinds)

    print(f'$( {qualified(thm)}, elaborated from {thm.path} by '
          f'parley/elaborate.py.')
    if work.axioms:
        print('   Everything is built except the statements below, which are')
        print('   taken as the readable lines state them: a closure method')
        print('   the elaborator does not expand, or a definition the')
        print('   database gives no target for.')
    else:
        print('   Nothing here is assumed.')
    say_library(setmm, library_size)
    print()
    # A theorem this corpus proves is cited as one label, so the file that
    # elaborated it is read first and the rest comes in through it. What is
    # underneath everything is the corpus's own definitions, which include
    # the library: one chain rather than one per proof. A file is included
    # by its path under elaboration/, which is its name.
    for name in work.cited:
        print(f'$[ {name}.mm $]')
    if not work.cited:
        # geometry.mm includes the definitions, so a proof that reaches one
        # of its labels needs only the one include; a proof that reaches
        # none does not read it at all.
        wants = provided & used
        print(f'$[ {GEOMETRY if wants else DEFINITIONS}.mm $]')
    print()
    for label, statement in work.axioms:
        print(f'{label} $a {statement} $.')
    if work.axioms:
        print()
    # Every variable the proof touches has to be disjoint from every other:
    # the lemmas that discharge a scope want the bound name apart from what
    # the theorem is about, and there is nothing here for them to collide in.
    held = {t for t in used if t in sigs and sigs[t].kind == '$f'}
    bound = sorted(sigs[t].statement[1] for t in held
                   if sigs[t].statement[0] == 'setvar')
    free = sorted(sigs[t].statement[1] for t in held
                  if sigs[t].statement[0] != 'setvar')
    print('${')
    # What a proof needs kept apart is a name it binds from everything
    # else. Two class variables are never one of those pairs, and saying
    # they are makes the theorem harder to cite than it is to prove: the
    # Bezout proof cites `least-combination-divides` at c := a, which a
    # blanket `$d` over every variable forbids.
    if len(bound) > 1:
        print('  $d ' + ' '.join(bound) + ' $.')
    for one in free:
        if bound:
            print(f'  $d {one} ' + ' '.join(bound) + ' $.')
    label = label_of(qualified(thm), sigs, thm.path, thm.line,
                     proved_here(items))
    says = (f'( {work.render(antecedent)} -> {work.render(goal)} )'
            if antecedent else work.render(goal))
    # Compressed, which is what set.mm is stored in and what `ELABORATION.md`
    # argued for: the corpus writes a scope into every line and a membership
    # wherever it is wanted, and normal format writes each of those out
    # again every time. The same proofs are 176 times smaller said this way.
    # The indices below the parentheses are the theorem's own hypotheses, in
    # the order the library declares them.
    mandatory = sorted({work.flabel[t] for t in says.split()
                        if t in work.flabel},
                       key=lambda one: work.forder[one])
    print(f'  {label} $p |- {says} $=')
    print(f'    {compressed(root, kinds, mandatory)} $.')
    print('$}')
    return 0


def report(argv):
    """`main`, with a defect said the way a person reads one.

    A `Problem` is somebody's to fix and knows where it is, so it is worth
    more than the traceback that used to carry it. A route declining is not
    one of those and never reaches here: `Elaborator.step` is where every
    route having declined becomes a defect, because that is where the step
    it was about is known.
    """
    try:
        return main(argv)
    except Problem as said:
        print(said, file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(report(sys.argv))

