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
`targets.MEMBERSHIP` names.

What is not expanded is stated at the head of the file it writes: a closure
method, or an item the database gives no target for. Each becomes an axiom
claiming exactly what the readable line claims, under the `requires` lines
that line carries and the lines it cites. Both, or the axiom says more than
the method does and the proof above it goes unused.

Usage:  parley/elaborate.py <theorem> <set.mm>
"""
import hashlib
import re
import sys
import typing
from fractions import Fraction
from pathlib import Path

import field
import kernel
import linear
import normal
import targets
from build import path_of
from formula import Grammar, Node, parse
from library import Signature
from library import read as read_library
from match import instantiation
from parse import (
    NAME,
    Problem,
    check_encoding,
    citations,
    fmt,
    parse_database,
    parse_proof,
)
from sorts import sorts_in_scope
from spell import Builder, seq

LABEL = re.compile(r'\s*\([A-Z]+[0-9]*\)\s*$')
# `let A be a set` introduces a name the way `let n ∈ ℕ` does, and states
# what `A is a set` states. The hypothesis line reads better as it is
# written; the claim is the notation the database declares. Points are the
# same shape, and every sort with a notation could be.
BE_A = re.compile(r'\s+be\s+a\s+(set|point)\b')
# Past the last line any proof has, for reading every define that is left.
_ENDLESS = float('inf')
CLASS_NAMES = ['cA', 'cB', 'cC', 'cD', 'cE', 'cF', 'cG', 'cH']
SPARE_VARS = ['vm', 'vk', 'vj', 'vi', 'vp', 'vq', 'vr', 'vs', 'vt', 'vu']
# The constructors that take a function, operation or relation as an operand.
WRAPS = ('co', 'wbr', 'cfv')
# Stands where a join would name the constructor, for a biconditional a
# lemma states the other way round from the way a step reaches it. It is no
# label, so a statement built from it would not spell, which is what stops a
# second antecedent being folded past one read this way.
TURNED = 'the other way round'
# What closes an induction, by the set the name inducted on runs over, and
# where that lemma starts. The two have the same six hypotheses in the same
# order and differ only in the set and the base, so choosing between them is
# choosing a label. Which one a proof wants is not the text's to say twice:
# `let n ∈ ℕ₀` already says it, and `starting at` is checked against it.
INDUCTION = {'cn': ('nnindd', 'c1'), 'cn0': ('nn0indd', 'cc0')}




def order_sides(goal):
    """The two sides of a claim and which relation stands between them."""
    if goal.variable is not None:
        return None
    if goal.label == 'wceq' and len(goal.children) == 2:
        return goal.children[0], goal.children[1], '='
    if goal.label != 'wbr' or len(goal.children) != 3:
        return None
    how = {'cle': '<=', 'clt': '<'}.get(goal.children[2].label)
    return None if how is None else (goal.children[0], goal.children[1], how)


def whole_multiple(cited, claim):
    """How many times the claim the cited equation is, if a whole number.

    Both are the polynomial that must vanish, so one being a multiple of
    the other is the two saying the same thing at different scales."""
    if cited is None or claim is None or not claim.terms:
        return None
    lead = max(claim.terms)
    if lead not in cited.terms:
        return None
    times = cited.terms[lead] / claim.terms[lead]
    if times.denominator != 1 or not 2 <= times.numerator <= 9:
        return None
    if cited.terms != claim.scaled(times).terms:
        return None
    return times.numerator


def declined(said):
    """Whether this is a route declining, or the proof text being wrong.

    `normal.Unhandled` is a route declining and says so. `Problem` is both:
    its docstring says it "carries where it was found", and the thirteen the
    elaborator raises where it cannot do something carry nowhere, while the
    forty-four it raises about the text carry a line.

    The difference matters where a method falls back to stating its step.
    A route declining should fall back; a defect in the text must not, or
    the step is listed as stated and the reader never sees the error. The
    two would be separate exceptions in a tidier program, and until they are
    the line is what tells them apart."""
    return not isinstance(said, Problem) or not said.line


def multiplier(shape, scale):
    """The term a combination multiplies one cited equation by, or None.

    `field.spell` writes the canonical polynomial, which raises an atom to
    the first power and multiplies it by one. That is what two polynomials
    being compared want and not what a factor wants: `( -u 1 x. ( q ^ 1 ) )`
    asks for two memberships nothing declares where `-u q` asks for one that
    is. So a multiplier is written the short way."""
    monomials = list(shape.terms)
    if len(monomials) != 1 or shape.terms[monomials[0]] != 1:
        return None
    parts = monomials[0]
    if not parts:
        return field.spell_coefficient(scale)
    if len(parts) != 1 or parts[0][1] != 1:
        return None
    name = parts[0][0]
    if scale == 1:
        return name
    if scale == -1:
        return seq(name, 'cneg')
    digit = field.spell_coefficient(scale)
    return None if digit is None else seq(digit, name, 'cmul', 'co')


def rescales(cited, claim):
    """What the cited polynomial is multiplied by to become the claim's.

    Two disequalities say one thing when one polynomial is the other
    scaled: `1 − a` is `−1` times `a − 1`, so `1 − a ≠ 0` and `a ≠ 1` deny
    the same number. Any nonzero rational will do, where `whole_multiple`
    wants a digit, because nothing here has to spell the scalar."""
    if cited is None or claim is None or not cited.terms or not claim.terms:
        return None
    lead = max(claim.terms)
    if lead not in cited.terms:
        return None
    times = claim.terms[lead] / cited.terms[lead]
    if times == 0 or claim.terms != cited.scaled(times).terms:
        return None
    return times


def hypothesis_body(kind, text):
    """What a hypothesis line claims, with its introduction read as one.

    `let A be a set` and `let P be a point` introduce a name and state what
    the sort means, and the notation that states it is what the database
    declares. The line reads better as it is written, so the substitution
    happens here and every reader of a hypothesis gets it."""
    body = text[len(kind):] if text.startswith(kind) else text
    if kind == 'let':
        body = BE_A.sub(lambda m: f' is a {m.group(1)}', body)
    return body


def label_of(name, taken=()):
    """What this elaborator calls a theorem it has written out.

    set.mm proves some of what this corpus proves and has its own names for
    them, so the label is moved off any that is already in use: `sqrt2irr`
    is taken. Which name it lands on depends only on set.mm, so a theorem
    that cites another agrees with the file that wrote it."""
    stem = name.replace('-', '')[:8]
    if stem not in taken:
        return stem
    for digit in range(1, 10):
        moved = f'{stem[:7]}{digit}'
        if moved not in taken:
            return moved
    raise Problem('', 0, f'no free label near {stem!r}')


class Fact:
    """A claim, a proof of it at one scope, and the sentences it was read from.

    A line may say several things, and a substitution may land in one of
    them, so what is kept is every sentence rather than the claim as one
    tree. A line read from no text at all keeps none."""

    def __init__(self, term, proof, sentences=()):
        self.term, self.proof, self.sentences = term, proof, sentences


class Block:
    """A block being elaborated: what it opened over and what it opened."""

    def __init__(self, owner, outer, facts, frame):
        self.owner, self.outer, self.outside = owner, outer, facts
        self.frame = frame          # index into the scope frames
        self.scope, self.facts = outer, facts
        self.supposed = None        # contradiction
        self.over = self.base = None                      # induction
        self.variable = None        # the setvar a fix introduced
        self.named = None           # the names in hand before it opened
        self.assumed = {}           # cases: part number -> what it assumes
        self.entered = None         # cases: the part now open
        self.claim = self.proof = None
        self.parts = {}             # part number -> the last fact in it


class Elaborator(Builder):
    # Which lemma rewrites a subterm, by what encloses it and which hole it
    # sits in. The tree decides; nothing is searched for.
    # A claim may change in more than one place at once — the claim of an
    # induction holds its variable several times — so the lemma is chosen by
    # which operands change together as well as by what encloses them.
    CONGRUENCE: typing.ClassVar = {
        ('co', (0,)): 'oveq1d', ('co', (1,)): 'oveq2d',
        ('co', (0, 1)): 'oveq12d',
        ('wbr', (0,)): 'breq1d', ('wbr', (1,)): 'breq2d',
        ('wbr', (0, 1)): 'breq12d',
        ('cfv', (0,)): 'fveq2d',
        ('wceq', (0,)): 'eqeq1d', ('wceq', (1,)): 'eqeq2d',
        ('wceq', (0, 1)): 'eqeq12d',
        ('wcel', (0,)): 'eleq1d', ('wcel', (1,)): 'eleq2d',
        ('wcel', (0, 1)): 'eleq12d',
        ('csu', (0,)): 'sumeq1d',
        ('cpw', (0,)): 'pweqd',
        ('wa', (0,)): 'anbi1d', ('wa', (1,)): 'anbi2d',
        ('wa', (0, 1)): 'anbi12d',
        ('w3a', (0,)): '3anbi1d', ('w3a', (1,)): '3anbi2d',
        ('w3a', (2,)): '3anbi3d', ('w3a', (0, 1, 2)): '3anbi123d',
        ('wn', (0,)): 'notbid',
        # A universal over an `if ... then` changes both sides at once when
        # the name it binds stands on each of them.
        ('wi', (0,)): 'imbi1d', ('wi', (1,)): 'imbi2d',
        ('wi', (0, 1)): 'imbi12d',
        ('wral', (0,)): 'ralbidv', ('wrex', (0,)): 'rexbidv'}

    # Which lemma discharges one thing a lemma asked, by how that thing was
    # joined to what follows it and whether the lemma is still bare. The
    # first is composed with the lemma itself; every later one is applied to
    # what the last already deduced.
    DISCHARGE: typing.ClassVar = {
        ('wi', True): 'syl', ('wi', False): 'mpd',
        ('wb', True): 'sylib', ('wb', False): 'mpbid'}

    # Which transitivity folds one link of a calculation into the run above
    # it, by what each of the two claims is. Two relations in a row would
    # want the transitivity of that relation and no chain writes one.
    FOLDING: typing.ClassVar = {
        ('wceq', 'wceq'): 'eqtrd', ('wceq', 'wbr'): 'eqbrtrd',
        ('wbr', 'wceq'): 'breqtrd'}

    def __init__(self, thm, grammar, items, sigs, records, theorems=()):
        super().__init__(sigs)
        self.thm, self.g, self.items = thm, grammar, items
        self.terms = targets.terms(records)
        # A name the proof introduces becomes a variable of the kernel, and it
        # must not be one a notation's own target binds: `S(_)` sums over `k`,
        # so a proof that fixes `k` cannot be given `k`.
        self.taken = {t for entries in self.terms.values()
                      for e in entries if e for t in e.split()}
        self.spare = [v for v in SPARE_VARS if v not in self.taken]
        self.commutes = targets.commuting(records)
        self.proofs = {t.name: t for t in theorems}
        self.cited = []          # corpus theorems this proof leans on
        self.joined = None
        self.enclosing = None    # the block a step sits directly inside
        self.shapes = {}         # target pattern -> the tree it reads as
        self.at = 0              # the line being elaborated, for `read`
        self.names = {}          # readable name -> kernel term
        self.fixed = {}          # the same, as the theorem's `let` lines left
                                 # it, for the names a notation holds fixed
        self.sets = {}           # readable name -> the set it was let into
        self.axioms = []         # (label, statement) for each algebra step
        self.reserved = set()    # setvars the conclusion quantifies over
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

    # --- terms --------------------------------------------------------------

    def read(self, text):
        """One sentence of the readable layer, as a tree.

        Where the elaborator has got to goes with it. A formula that does
        not parse is a defect and wants somewhere to point; without a
        position it arrived looking like a route declining, and a `requires`
        line nobody could read was taken as stated instead of reported."""
        return parse(LABEL.sub('', text).strip(), self.g,
                     self.thm.path, self.at)

    def term(self, node):
        if node.notation == 'literal':
            return node.term
        if node.notation == 'name':
            if node.text not in self.names:
                raise Problem('', 0, f'no kernel name for {node.text!r}')
            return self.names[node.text]
        if node.notation == 'numeral':
            return targets.NUMERALS[node.text]
        # A binder's first hole is the variable it introduces, which stands
        # for itself rather than for whatever a name is bound to.
        bound = self.binders.get(node.notation, ())
        saved = dict(self.names)
        for i in bound:
            # The body speaks of what the binder introduces, so the name
            # stands for its own variable while the body is read.
            said = node.children[i].text
            self.names[said] = f'{self.binder_var(said)} cv'
        holes = [self.binder_var(c.text) if i in bound else self.term(c)
                 for i, c in enumerate(node.children)]
        if bound:
            self.names = saved
        return targets.fill(self.pattern(node), holes, self.held(node))

    def held(self, node):
        """What each name this notation holds fixed stands for.

        Read from what the theorem fixed rather than from the names in hand,
        so the answer is the same wherever the notation is written. A proof
        that never fixes the name cannot write the notation at all, which is
        what being local to a definition means."""
        out = {}
        for name in targets.fixes(self.pattern(node)):
            if name not in self.fixed:
                raise Problem('', 0,
                              f'notation {node.notation!r} is about {name!r}, '
                              f'which this theorem does not fix')
            out[name] = self.fixed[name]
        return out

    def spelling(self, node):
        """The node's target with what it holds fixed already resolved.

        A shape is read from this rather than from the target as written,
        because a fixed name is a term of the theorem's and not a hole: a
        rewrite walks past it the way it walks past a constant."""
        pattern, fixed = self.pattern(node), self.held(node)
        return (targets.FIXED.sub(lambda m: fixed[m.group(1)], pattern)
                if fixed else pattern)

    def pattern(self, node):
        """The `target` entry of the pattern this node was built from."""
        entries = self.terms.get(node.notation)
        if entries is None:
            raise Problem('', 0,
                          f'notation {node.notation!r} has no target field')
        order = self.literals.get(node.notation, [])
        found = entries[order.index(node.text)] if node.text in order \
            else entries[0]
        if found is None:
            raise Problem('', 0,
                          f'notation {node.notation!r} builds no term here')
        return found

    # --- closure ------------------------------------------------------------

    def closure(self, node, want, scope, facts):
        """A proof that this term lies in `want`.

        The readable proof writes a `requires` line saying which fact it
        needs and which item supplies it. What it never writes is how to
        build that fact for a compound term, because to a reader that is
        not a step. It is settled the way every side condition is, from the
        lemmas `targets.MEMBERSHIP` names: putting a sum of integers in ZZ
        and putting a summation index in CC are one question asked twice."""
        goal = seq(self.term(node), want, 'wcel')
        if goal in facts:
            return facts[goal]
        return self.settle(self.to_term(goal), scope, facts)

    # --- facts the text never writes ----------------------------------------

    def to_term(self, rpn):
        """A term the proof holds, read back as a tree."""
        stack = []
        for token in rpn.split():
            sig = self.sigs[token]
            if sig.kind == '$f':
                stack.append(kernel.Term(variable=sig.statement[1]))
                continue
            count = len(sig.floats)
            args = stack[len(stack) - count:] if count else []
            del stack[len(stack) - count:]
            stack.append(kernel.Term(token, tuple(args)))
        return stack[0]

    def settle(self, wanted, scope, facts, depth=5, step=None, lines=None):
        """A proof of something a step needs and the text does not write.

        A cited lemma asks side conditions of its own — that an index is in
        the upper integers, that a summand is complex — and those are not
        `requires` lines, because to a reader they are not steps. They are
        settled from the lemmas `targets.MEMBERSHIP` names, by matching what
        each concludes against what is wanted.

        A step is passed only where one is there to have cited a witness,
        which is what lets an existential be proved at all. Side conditions
        pass none, so they stay what they are: settled from declared
        lemmas, never by finding a fact that happens to fit."""
        rpn = wanted.rpn(self.flabel)
        if rpn in facts:
            return facts[rpn]
        if depth > 0:
            if wanted.label in ('wa', 'w3a'):
                kids = [c.rpn(self.flabel) for c in wanted.children]
                return seq(scope, *kids,
                           *(self.settle(c, scope, facts, depth - 1,
                                         step, lines)
                             for c in wanted.children),
                           'jca' if wanted.label == 'wa' else '3jca')
            if wanted.label == 'wrex' and step is not None:
                return self.witnessed(step, wanted, scope, facts,
                                      lines or {})
            # Every lemma is tried as it is written before any is read
            # backwards, so that a biconditional turned round never stands
            # in for one that says what is wanted outright.
            for backwards in (False, True):
                for label in targets.MEMBERSHIP:
                    sig = self.sigs.get(label)
                    if sig is None or sig.essentials:
                        continue
                    found = self.fits(label, sig, wanted, scope, facts,
                                      depth, backwards)
                    if found is not None:
                        return found
        raise Problem('', 0, f'cannot settle {self.render(rpn)}')

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
        the same way a bare biconditional is."""
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
        biconditional has one of each and they do not discharge alike."""
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
        # antecedent still open is matched against something already known.
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
                return None

        proof = self.ap(label, self.spelt(binding))
        if not antecedents:
            return seq(wanted.rpn(self.flabel), scope, proof, 'a1i')
        try:
            for i, slot in enumerate(antecedents):
                asks = slot.substitute(binding)
                rest = wanted.rpn(self.flabel)
                for later, join in reversed(list(zip(antecedents[i + 1:],
                                                     joins[i + 1:],
                                                     strict=True))):
                    said = later.substitute(binding).rpn(self.flabel)
                    # A biconditional read backwards states its sides the
                    # other way round from the order they are taken in.
                    rest = (seq(rest, said, 'wb')
                            if join == 'wb' and backwards
                            else seq(said, rest, join))
                first = proof.split()[-1] == label
                fold = self.DISCHARGE[(joins[i], first)]
                if joins[i] == 'wb' and backwards:
                    fold = 'sylibr' if first else 'mpbird'
                proof = seq(scope, asks.rpn(self.flabel), rest,
                            self.settle(asks, scope, facts, depth - 1), proof,
                            fold)
        except Problem:
            return None
        return proof

    # --- congruence ---------------------------------------------------------

    def shape(self, pattern):
        """A target read as a tree, so a rewrite can walk down it.

        A target need not be one constructor. `S(_)` is a sum over a range
        that holds the hole, so reaching the hole passes a `csu` and then a
        `co`, and each level wants its own congruence lemma."""
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
            if token in WRAPS:                # the operation is an operand
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
        return seq(*parts, label, wrap) if wrap else seq(*parts, label)

    def rewrite(self, node, old, new, scope, eqproof):
        """A proof that `node` equals `node` with `old` replaced by `new`.

        The path from the root of the claim to the occurrence decides the
        lemmas, one per step along it, and which hole the occurrence sits in
        decides which lemma. Nothing is searched for."""
        if self.term(node) == old:
            return new, eqproof
        # A binder's variable fills its slot as itself, and nothing rewrites
        # it: the claim is about what the binder ranges over, not about the
        # name it ranges under.
        bound = self.binders.get(node.notation, ())
        holes = [self.binder_var(c.text) if i in bound else self.term(c)
                 for i, c in enumerate(node.children)]
        after, proofs = list(holes), {}
        for i, child in enumerate(node.children):
            if i in bound or old not in self.term(child):
                continue
            after[i], proofs[i] = self.rewrite(child, old, new, scope,
                                               eqproof)
        if not proofs:
            raise Problem('', 0, f'nothing to rewrite in {self.term(node)}')
        return self.descend(self.shape(self.spelling(node)), holes, after,
                            proofs, scope)

    def descend(self, tree, before, after, proofs, scope):
        """Walk a target down to the holes that changed, a lemma a level."""
        if tree[0] == 'hole':
            return after[tree[1]], proofs[tree[1]]
        if tree[0] == 'const':
            raise Problem('', 0, 'no hole changed under this target')
        _k, label, wrap, kids = tree
        was = [self.spell(k, before) for k in kids]
        now, deeper, slots = list(was), [], []
        for slot, kid in enumerate(kids):
            if not any(self.holds(kid, h) for h in proofs):
                continue
            now[slot], under = self.descend(kid, before, after, proofs, scope)
            deeper.append(under)
            slots.append(slot)
        if not slots:
            raise Problem('', 0, 'no hole changed under this target')
        # An operation or a relation is itself an operand of the lemma that
        # rewrites under it; a constructor that takes its arguments directly
        # is not. What changed comes first, old beside new, then the rest.
        moved = [x for slot in slots for x in (was[slot], now[slot])]
        rest = [o for j, o in enumerate(was) if j not in slots]
        built = seq(*now, label, wrap) if wrap else seq(*now, label)
        return built, seq(scope, *moved, *rest, label if wrap else '',
                          *deeper, self.CONGRUENCE[(wrap or label,
                                                    tuple(slots))])

    # --- definitions --------------------------------------------------------

    def flip(self, node):
        """The same equality with its sides the other way round."""
        return Node(node.notation, node.sort, list(reversed(node.children)),
                    node.text)

    def definition(self, name, subject, var=None):
        """A definition's right side, as nodes, with its names bound.

        Returns the unfolding lemma, the bound variable, the node the
        existential quantifies, and what it quantifies over. The body is
        returned facing the way the lemma writes it, which is not always the
        way the text writes it."""
        item = self.items[name.split(':', 1)[1]]
        lemma, flipped = targets.unfolding(item)
        if lemma is None:
            raise Problem('', 0, f'{name} has no target field')
        var = var or self.flabel[self.sigs[lemma].bound()]
        node = self.read(item.conclusions[0][0])
        left, right = node.children
        self.names[self.subject_of(left).text] = subject
        self.names[right.children[0].text] = f'{var} cv'
        body = right.children[2]
        return (lemma, var, self.flip(body) if flipped else body, body,
                self.term(right.children[1]), self.term(left))

    def unfolding(self, step, lemma, left, ex, var, over, scope, facts,
                  hint=None):
        """The biconditional a definition's lemma gives, in scope.

        A target need not take only the thing being defined, and need not ask
        only that it lie somewhere: `divides` unfolds `d || n` and wants both
        d and n in ZZ. Which of the lemma's variables the readable left side
        fills, and what the lemma then asks for, are read off its statement
        rather than assumed of it.

        Returns the proof and the right side it reached. `ex` is the wording
        the step wants; pass None to take whatever the lemma says."""
        sig = self.sigs[lemma]
        whole = self.syntax.statement(sig)
        asks, reads = [], whole
        while reads.label == 'wi':
            asks.append(reads.children[0])
            reads = reads.children[1]
        if reads.label != 'wb':
            raise Problem('', step.line, f'{lemma} states no biconditional')
        binding = kernel.match(reads.children[0], self.to_term(left), {},
                               whole.names())
        if binding is None:
            raise Problem('', step.line,
                          f'{lemma} does not unfold {self.render(left)}')
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
        says = seq(left, given, 'wb')
        if not asks:
            proof = seq(says, scope, applied, 'a1i')
        else:
            holds = asks[0].substitute(binding).rpn(self.flabel)
            proof = self.required(step, holds, over, scope, facts)
            for slot in asks[1:]:
                extra = slot.substitute(binding).rpn(self.flabel)
                proof = seq(scope, holds, extra, proof,
                            self.required(step, extra, over, scope, facts),
                            'jca')
                holds = seq(holds, extra, 'wa')
            proof = seq(scope, holds, says, proof, applied, 'syl')
        if ex is None or given == ex:
            return proof, given
        return seq(scope, left, given, ex, proof,
                   self.bridging(self.to_term(given), self.to_term(ex), scope,
                                 facts, step),
                   'bitrd'), ex

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
        last one proved."""
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
            if found:
                break
        else:
            raise Problem('', step.line, 'no cited line names a witness for '
                          f'{self.render(wanted.rpn(self.flabel))}')

        proof = facts.get(cited.term, cited.proof)
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
            instance = self.prove_essential(
                self.to_term(seq(seq(mark, witness, 'wceq'),
                                 seq(ph, ps, 'wb'), 'wi')), scope, facts)
            member = seq(witness, over, 'wcel')
            proof = seq(scope, seq(member, ps, 'wa'), seq(ph, var, over,
                                                          'wrex'),
                        seq(scope, member, ps,
                            self.required(step, member, over, scope, facts),
                            proof, 'jca'),
                        ph, ps, var, witness, over, instance, 'rspcev', 'syl')
        return proof

    def restated(self, term, was, now):
        """`term` with every occurrence of the subterm `was` reading `now`.

        Both are given in reverse Polish, because a term is compared by what
        it spells: the kernel's terms are trees without an equality."""
        if term.rpn(self.flabel) == was:
            return self.to_term(now)
        if term.variable is not None:
            return term
        return kernel.Term(term.label,
                           tuple(self.restated(c, was, now)
                                 for c in term.children))

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
        which is false."""
        out = dict(binding)
        for text in sig.essentials:
            asked = self.syntax.parse(text[1:], 'wff')
            if asked.label != 'wi':
                continue
            at, says = asked.children
            if (at.label != 'wceq' or says.label != 'wb'
                    or at.children[0].label != 'cv'):
                continue
            name = says.children[1].variable
            if name is None:
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
        equation, and an equation is settled like anything else."""
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
        the same number but not the same formula."""
        def swapped(one, other, where, held):
            if not self.exchanged(one, other):
                return None
            return self.settle(self.to_term(
                seq(one.rpn(self.flabel), other.rpn(self.flabel), 'wceq')),
                where, held)
        return self.congruence(given, want, scope, facts, step, swapped)

    def congruence(self, given, want, scope, facts, step, leaf):
        """Carry one change up to the whole term it sits in.

        Two terms that differ in one place are walked in step, and the
        lemma that lifts each level is the one the tree names: the walk
        `descend` makes over a readable claim, made here over a term the
        kernel holds. What counts as the change, and what proves it there,
        is the caller's."""
        line = step.line if step else 0
        found = leaf(given, want, scope, facts)
        if found is not None:
            return found
        if (given.label != want.label
                or len(given.children) != len(want.children)):
            raise Problem('', line,
                          f'{self.render(given.rpn(self.flabel))} and '
                          f'{self.render(want.rpn(self.flabel))} differ by '
                          'more than the change being carried')
        if given.label == 'wrex':
            body, variable, over = given.children
            name, runs = variable.rpn(self.flabel), over.rpn(self.flabel)
            member = seq(f'{name} cv', runs, 'wcel')
            inner, lifted = self.widen(scope, facts, member)
            return seq(scope, body.rpn(self.flabel),
                       want.children[0].rpn(self.flabel), name, runs,
                       self.congruence(body, want.children[0], inner, lifted,
                                       step, leaf),
                       'rexbidva')
        wrapped = given.label in WRAPS
        kids = given.children[:-1] if wrapped else given.children
        wants = want.children[:-1] if wrapped else want.children
        spelt = [c.rpn(self.flabel) for c in kids]
        other = [c.rpn(self.flabel) for c in wants]
        slots = [i for i in range(len(kids)) if spelt[i] != other[i]]
        if not slots:
            raise Problem('', line, 'nothing changed under this term')
        moved = [x for i in slots for x in (spelt[i], other[i])]
        rest = [s for i, s in enumerate(spelt) if i not in slots]
        head = given.children[-1].rpn(self.flabel) if wrapped else ''
        return seq(scope, *moved, *rest, head,
                   *(self.congruence(kids[i], wants[i], scope, facts, step,
                                     leaf)
                     for i in slots),
                   self.CONGRUENCE[(given.label, tuple(slots))])

    @staticmethod
    def subject_of(node):
        while node.children:
            node = node.children[0]
        return node

    # --- the proof ----------------------------------------------------------

    def sentences(self, text):
        out = []
        for piece in LABEL.sub('', text).strip().split('. '):
            piece = piece.strip().rstrip('.').strip()
            if piece:
                out.append(piece)
        return out

    def claim_of(self, text):
        """A claim of several sentences is their conjunction.

        `then x ≤ |x|. −x ≤ |x|.` states two things at once, and the kernel
        has one conclusion, so the sentences are conjoined in the order the
        text writes them."""
        said = [self.term(self.read(s)) for s in self.sentences(text)]
        whole = said[0]
        for extra in said[1:]:
            whole = seq(whole, extra, 'wa')
        return whole

    def hypotheses(self):
        """Name every `let` variable, and read the hypotheses.

        A `let` introduces a name and says what it ranges over. `let n ∈ ℕ`
        says it with a membership, `let A be a set` with no set at all, and
        `let f : A → 𝒫A` by saying what the name maps between. All three
        name the thing they introduce first, so all three are read the same
        way: name the leftmost leaf, then read the line as a claim about
        it."""
        nodes, spare = [], list(CLASS_NAMES)
        for kind, text, _label, _line in self.thm.hypotheses:
            node = self.read(hypothesis_body(kind, text))
            if kind == 'let':
                introduced = self.subject_of(node)
                if introduced.text and introduced.text not in self.names:
                    self.names[introduced.text] = spare.pop(0)
                if node.notation == 'membership':
                    self.sets[introduced.text] = self.term(node.children[1])
            nodes.append(node)
        return nodes

    def defined(self, before):
        """Bind what every `define` above line `before` stands for.

        A define is an abbreviation and nothing more: Cantor names a set B
        and every line about B is a line about the set-builder it names. So
        the name is bound to that term and the proof never carries it, which
        is also what keeps it apart from the B the conclusion quantifies
        over — those are two different things spelt the same way.

        It is read where it stands, which is what the parser's own comment
        says of it. One written above the first step names what the theorem
        fixes and is in hand before anything else; one written inside a
        block names what the block introduced, and the subsets proof has
        two of those, eighteen columns in, over an X a `fix` fixed and an
        `a` an `obtain` obtained. Read at the top they find neither.

        A block gives its names back when it closes, and these go with
        them."""
        while self.unread < len(self.thm.defines):
            _kind, text, label, line = self.thm.defines[self.unread]
            if line >= before:
                return
            self.unread += 1
            said = LABEL.sub('', text[len('define'):]).strip()
            name, _, body = said.partition(':=')
            name = name.strip()
            if not body.strip():
                raise Problem('', line, f'define {label} says nothing')
            if name in self.names:
                raise Problem('', line, f'{name} is already named')
            self.names[name] = self.apart(self.term(self.read(body.strip())))

    def apart(self, rpn):
        """A term whose bound names are ones nothing else is using.

        A `define` names a thing by a body that binds a name of its own,
        and the proof may go on to fix a name spelt the same way: Cantor's
        B collects the x that its own image leaves out, and then fixes an x
        to reason about. Those are two names, and the kernel has to see two
        or the lemma that generalises over one will find the other.

        Only the names the body binds. A body may also mention a name the
        proof is already holding — the subsets proof defines U as the power
        set of X without the `a` it obtained — and renaming that one would
        make the definition speak of some other element."""
        whole = self.to_term(rpn)
        binding = {}
        holds = {t.split()[0] for t in self.names.values()
                 if isinstance(t, str) and t.endswith(' cv')}
        for said in sorted(whole.names()):
            label = self.flabel.get(said)
            if label and label not in holds \
                    and self.sigs[label].statement[0] == 'setvar':
                fresh = self.spare_var()
                binding[said] = kernel.Term(
                    variable=self.sigs[fresh].statement[1])
        return whole.substitute(binding).rpn(self.flabel)

    def run(self):
        nodes = self.hypotheses()
        # A notation may hold a name no hole of it fills, and that name is
        # bound where the definition introducing it stands rather than where
        # the notation is written: `def:G` says `let a ∈ ℝ`, and every `G(n)`
        # below is about that `a`. The theorem's `let` lines are that place,
        # and they are read before its conclusion and before any step, so
        # what is taken here is what the text fixed. Nothing writes it again,
        # which is what stops a block binding the same letter from reaching
        # it.
        self.fixed = dict(self.names)
        # What stands above the first step is the theorem's own, and the
        # hypotheses and the conclusion below may lean on it.
        self.defined(self.thm.steps[0].line if self.thm.steps else _ENDLESS)
        terms = [self.term(n) for n in nodes]
        # A theorem may assume nothing, and every step here is still an
        # implication out of the scope it sits in. So the scope is truth,
        # which is discharged once at the end.
        scope = terms[0] if terms else 'wtru'
        facts = {scope: seq(scope, 'id')}
        for extra in terms[1:]:
            wider = seq(scope, extra, 'wa')
            facts = {k: seq(wider, scope, k, seq(scope, extra, 'simpl'), v,
                            'syl')
                     for k, v in facts.items()}
            facts[extra] = seq(scope, extra, 'simpr')
            scope = wider
        # A hypothesis may say several things at once — `A, B, C form a
        # triangle` says three — and each of them is a fact the proof may
        # lean on without a step to take it apart.
        for extra in terms:
            if extra in facts:
                self.unpack(extra, facts[extra], scope, facts)

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
            if step.openers or step.parts:
                block = self.open_block(step, scope, facts, lines)
                block.opened_at = len(closers)
                blocks.append(block)
                scope, facts = block.scope, block.facts
                continue
            if blocks and blocks[-1].assumed and step.part is not None:
                scope, facts = self.enter_case(blocks[-1], step.part, lines)
            self.enclosing = blocks[-1] if blocks else None
            scope, facts, closers = self.step(step, scope, facts, lines,
                                              closers)
            if step.part is not None and blocks:
                held = lines[self.last]
                blocks[-1].parts[step.part] = (held.term, held.proof)
        while blocks:
            done = blocks.pop()
            scope, facts, closers = self.close_block(done, facts, lines,
                                                     closers, scope)
            self.hand_up(done, blocks)

        proof = lines[self.last].proof
        for close in reversed(closers):
            proof = close(proof, goal)
        return goal, terms, proof

    def widen(self, scope, facts, added):
        """Conjoin one more thing onto the antecedent, carrying the facts.

        This is what every block form does when it opens: `ELABORATION.md`
        requirement 1. The frame is kept so that a step whose lemma forbids
        the innermost assumption can be proved without it."""
        inner = seq(scope, added, 'wa')
        lifted = {k: seq(inner, scope, k, seq(scope, added, 'simpl'), v, 'syl')
                  for k, v in facts.items()}
        lifted[added] = seq(scope, added, 'simpr')
        self.unpack(added, lifted[added], inner, lifted)
        # Each frame keeps what is known at it, because a step whose lemma
        # forbids an inner assumption is proved at an outer one.
        self.frames.append((inner, added, lifted))
        return inner, lifted

    # A fact that conjoins several things says each of them, and the steps
    # below cite them one at a time: an `obtain` hands over one body saying
    # that q is positive, that x is p over q, and that nothing divides both.
    SPLIT: typing.ClassVar = {'wa': ('simpl', 'simpr'),
                              'w3a': ('simp1', 'simp2', 'simp3')}

    def unpack(self, term, proof, scope, facts, depth=4):
        """Record each conjunct of a fact as a fact of its own."""
        if depth <= 0:
            return
        node = self.to_term(term)
        picks = self.SPLIT.get(node.label)
        if not picks or len(picks) != len(node.children):
            return
        kids = [c.rpn(self.flabel) for c in node.children]
        for part, pick in zip(kids, picks, strict=True):
            if part in facts:
                continue
            facts[part] = seq(scope, term, part, proof, *kids, pick, 'syl')
            self.unpack(part, facts[part], scope, facts, depth - 1)

    def open_block(self, step, scope, facts, lines):
        """A block's assumption is conjoined onto the antecedent.

        All four block forms do this; what differs is the lemma that closes
        them. `ELABORATION.md` requirement 1."""
        head = step.just.head
        block = Block(step, scope, facts, len(self.frames) - 1)
        # Taken before the block names anything, so that what it names is
        # what closing it gives back.
        block.named = dict(self.names)
        if head == 'contradiction':
            kind, text, label, _l, _p = step.openers[0]
            node = self.read(hypothesis_body(kind, text))
            block.supposed = self.term(node)
            block.scope, block.facts = self.widen(scope, facts,
                                                  block.supposed)
            if label:
                lines[label] = Fact(block.supposed,
                                    block.facts[block.supposed], (node,))
            self.joined = None
        elif head == 'fix':
            block.scope, block.facts = scope, facts
            for kind, text, label, _l, _p in step.openers:
                body = hypothesis_body(kind, text)
                if kind == 'let':
                    # A fixed name is a variable of the kernel, not a class,
                    # and it must avoid whatever the notations bind: the sum
                    # binds `k`, so a proof that fixes `k` cannot use it.
                    node = self.read(body)
                    name = node.children[0].text
                    block.variable = self.fixed_var(name)
                    self.names[name] = f'{block.variable} cv'
                    # `let X be a set` fixes a name over nothing and says
                    # only that it is a set, so there is no set to record,
                    # the same way `hypotheses` reads it at the head.
                    if node.notation == 'membership':
                        self.sets[name] = self.term(node.children[1])
                node = self.read(body)
                added = self.term(node)
                block.scope, block.facts = self.widen(block.scope,
                                                      block.facts, added)
                if label:
                    lines[label] = Fact(added, block.facts[added], (node,))
        elif head == 'cases':
            # Every other block opens one scope for all its children. A
            # `cases` opens one per part, so nothing is widened here and the
            # part is entered when its first child arrives.
            block.scope, block.facts = scope, facts
            block.assumed = {}
            for kind, text, label, _l, part in step.openers:
                body = hypothesis_body(kind, text)
                block.assumed[part] = (self.read(body), label)
        elif head == 'induction':
            block.scope, block.facts = scope, facts
            block.over = re.search(r'induction on (\S+)',
                                   step.just.text).group(1)
            block.base = self.spare_var()
        else:
            raise Problem('', step.line,
                          f'no expansion for a {head} block')
        return block

    def enter_case(self, block, part, lines):
        """Open the scope one case of a `cases` block runs under."""
        if block.entered == part:
            return block.scope, block.facts
        del self.frames[block.frame + 1:]
        # A case gives back what it named, the way the block does when it
        # closes: the next one starts from where the block started, and the
        # assumption below is read against that and not against whatever
        # the case before it left behind.
        self.names = dict(block.named)
        node, label = block.assumed[part]
        assumed = self.term(node)
        block.scope, block.facts = self.widen(block.outer, block.outside,
                                              assumed)
        block.entered = part
        if label:
            lines[label] = Fact(assumed, block.facts[assumed], (node,))
        return block.scope, block.facts

    @staticmethod
    def hand_up(done, blocks):
        """A closed block is the result of the part of its parent it sits in."""
        if done.owner.part is not None and blocks:
            blocks[-1].parts[done.owner.part] = (done.claim, done.proof)
            if done.variable:
                blocks[-1].variable = done.variable

    def close_block(self, block, facts, lines, closers, deep):
        """What a block gives back, by the lemma its kind closes with.

        An `obtain` inside a block does not discharge where the proof ends:
        it discharges where the block does, since the lemma that closes the
        block wants what the block holds and not what the obtain's scope
        holds. So the closers raised inside a contradiction are spent on it,
        and only what is left over reaches the end of the proof."""
        step = block.owner
        head = step.just.head
        inside = closers[block.opened_at:]
        # A block gives back its scope and its names together: the frames it
        # pushed, and whatever it fixed, obtained or defined inside.
        del self.frames[block.frame + 1:]
        self.names = dict(block.named)
        if head == 'contradiction':
            block.claim, block.proof = self.close_contradiction(
                block, facts, inside, deep, lines)
            closers = closers[:block.opened_at]
        elif head == 'fix':
            held = lines[self.last]
            block.claim, block.proof = held.term, held.proof
            if step.part is not None:
                return block.outer, block.outside, closers   # the induction
            # A fix standing on its own is a generalisation: it fixed a name,
            # said something about it, and the block claims that of every
            # such name. Inside an induction the same block is one part of
            # it, and the induction takes it as it stands.
            block.claim, block.proof = self.close_fix(block, held)
        elif head == 'cases':
            block.claim, block.proof = self.close_cases(block, lines)
        elif head == 'induction':
            block.claim, block.proof = self.close_induction(block, lines)
        number = '.'.join(str(p) for p in step.number)
        outer = dict(block.outside)
        outer[block.claim] = block.proof
        lines[number] = Fact(block.claim, block.proof)
        self.last = number
        return block.outer, outer, closers

    def close_contradiction(self, block, facts, inside, deep, lines):
        """A contradiction closes on the pair its `join` named.

        The contradiction is struck where the two lines are, and only then
        is anything discharged: the pair 3.16 and 3.1 names p and q, and an
        existential over p and q cannot be discharged around a claim that
        still mentions them. So pm2.21dd takes the pair to the block's claim
        first, the obtains raised inside the block discharge that, and the
        supposition is dropped last. The join itself emits nothing: this
        consumes both lines.

        Which lemma drops the supposition depends on which of the two is
        the negation. Supposing √2 rational to show it is not is pm2.01d;
        supposing p is not above n to show that it is, as the primes proof
        does, is pm2.18d and reaches the claim itself rather than a double
        negation of it.

        A joined line may say several things at once — 3.1 names p and q and
        says in the same breath that nothing above 1 divides both — so the
        pair is looked for among the parts of the two lines rather than
        between the lines whole."""
        step, scope, supposed = block.owner, block.outer, block.supposed
        if not self.joined:
            raise Problem('', step.line, 'the block closes on no join')
        held = lines.get(self.last)
        found = self.opposing([*self.joined,
                               *([held.term] if held else [])], facts, deep)
        if found is None:
            raise Problem('', step.line,
                          'the joined lines are not a contradiction')
        first, second, known = found
        claim = self.claim_of(' '.join(step.claim))
        proof = seq(deep, first, claim, known[first], known[second],
                    'pm2.21dd')
        for close in reversed(inside):
            proof = close(proof, claim)
        lifted = seq(scope, supposed, claim, proof, 'ex')
        if claim == seq(supposed, 'wn'):
            return claim, seq(scope, supposed, lifted, 'pm2.01d')
        if supposed == seq(claim, 'wn'):
            return claim, seq(scope, claim, lifted, 'pm2.18d')
        raise Problem('', step.line,
                      'the block claims neither its supposition negated nor '
                      'what its supposition denies')

    def opposing(self, lines, facts, scope):
        """A claim and its negation, among the parts of what the block holds.

        What holds the pair differs by proof: the √2 proof joins two lines
        that each say one thing, and Cantor's cases give back a single line
        saying both. So every part of every line offered is a candidate, and
        a line saying several things is taken apart first."""
        known = dict(facts)
        for line in lines:
            if line in known:
                self.unpack(line, known[line], scope, known)
        seen = [t for line in lines for t in self.parts(line) if t in known]
        for one in seen:
            for other in seen:
                if other == seq(one, 'wn'):
                    return one, other, known
        return None

    def parts(self, term):
        """A fact and every conjunct inside it, the whole one first."""
        yield term
        node = self.to_term(term)
        picks = self.SPLIT.get(node.label)
        if picks and len(picks) == len(node.children):
            for child in node.children:
                yield from self.parts(child.rpn(self.flabel))

    def close_fix(self, block, held):
        """A fix closed by generalising over the name it fixed.

        ralrimiva wants what was proved under the name, said out of the
        scope the block opened over. Which name and which set are read off
        the claim the block states, since that is what the text wrote."""
        step = block.owner
        claim = self.claim_of(' '.join(step.claim))
        whole = self.to_term(claim)
        if whole.label != 'wral':
            raise Problem('', step.line,
                          'a fix that claims nothing of every such name')
        body, variable, over = whole.children
        if body.rpn(self.flabel) != held.term:
            raise Problem('', step.line,
                          'the block does not reach what it claims of the '
                          'name it fixed')
        return claim, seq(block.outer, held.term,
                          variable.rpn(self.flabel), over.rpn(self.flabel),
                          held.proof, 'ralrimiva')

    def close_cases(self, block, lines):
        """Two cases and the disjunction that says one of them holds.

        mpjaodan wants each case as an implication out of the scope with its
        own assumption conjoined, which is what each part was proved as, and
        the disjunction the block cites. The fourth and last block form, and
        the same shape as the other three: widen, prove, close with one
        lemma."""
        step, scope = block.owner, block.outer
        if set(block.parts) != set(block.assumed):
            raise Problem('', step.line, 'a case of the block proves nothing')
        claim = self.claim_of(' '.join(step.claim))
        parts = sorted(block.assumed)
        first, second = (self.term(block.assumed[p][0]) for p in parts)
        said = [block.parts[p][1] for p in parts]
        return claim, seq(scope, first, claim, second, *said,
                          self.carried(step.just.refs[0], block.outside,
                                       lines),
                          'mpjaodan')

    def close_induction(self, block, lines):
        """Induction closes with the lemma for the set it runs over.

        Whichever it is wants the claim five ways and the text writes none
        of them: it says only which name to induct on and where to start. So
        the claim is read as a function of that name and instantiated, and
        each instance is tied to the general one by congruence.
        `ELABORATION.md` requirement 13."""
        step, scope = block.owner, block.outer
        if set(block.parts) != {0, 1}:
            raise Problem('', step.line, 'induction wants a base and a step')
        (_base_claim, base), (step_claim, stepped) = (block.parts[0],
                                                      block.parts[1])
        name, general = block.over, f'{block.base} cv'
        over = self.sets.get(name)
        if over not in INDUCTION:
            raise Problem('', step.line,
                          f'nothing here inducts over {self.render(over)}'
                          if over else
                          f'nothing says what {name} runs over')
        lemma, begins = INDUCTION[over]
        at = re.search(r'starting at ([^\s,]+)', step.just.text)
        start = self.term(self.read(at.group(1))) if at else begins
        if start != begins:
            raise Problem('', step.line,
                          f'an induction over {self.render(over)} starts at '
                          f'{self.render(begins)}, and the text says '
                          f'{self.render(start)}')
        variable = block.variable or self.spare_var()
        next_one = seq(f'{variable} cv', 'c1', 'caddc', 'co')

        saved = dict(self.names)
        self.names[name] = general
        pattern = self.freeze(self.read(' '.join(step.claim)))
        self.names = saved
        shapes = [start, f'{variable} cv', next_one, self.names[name]]
        instances, ties = [], []
        for value in shapes:
            here = seq(general, value, 'wceq')
            built, proof = self.rewrite(pattern, general, value, here,
                                        seq(here, 'id'))
            instances.append(built)
            ties.append(proof)
        claimed, held, reached, whole = instances
        member = seq(self.names[name], self.sets[name], 'wcel')
        body = self.term(pattern)

        run = seq(scope, body, claimed, held, reached, whole,
                  block.base, variable, self.names[name], *ties, base,
                  stepped, lemma)
        if step_claim != reached:
            raise Problem('', step.line,
                          'the step does not reach the next instance')
        # The lemma states the membership apart from the rest of the
        # antecedent, and the scope already holds it, so the two are
        # conjoined back.
        if member not in block.outside:
            raise Problem('', step.line,
                          f'nothing in scope says {member}')
        return whole, seq(scope, seq(scope, member, 'wa'), whole,
                          seq(scope, scope, member, seq(scope, 'id'),
                              block.outside[member], 'jca'),
                          run, 'syl')

    def step(self, step, scope, facts, lines, closers):
        head = step.just.head
        number = '.'.join(str(p) for p in step.number)
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
            item = self.items[head.split(':', 1)[1]]
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
            raise Problem('', step.line, f'no expansion for {head!r}')
        proof = how(step, node, term, scope, facts, lines)
        if proof is None:                  # a join, which emits nothing
            return scope, facts, closers
        lines[number] = Fact(term, proof, self.said(step))
        facts[term] = proof
        return scope, facts, closers

    def said(self, step):
        """Every sentence of a step's claim, as trees.

        `node` above is the last of them, because that is what an expansion
        is about. A line is cited whole, so what it keeps is all of them."""
        return tuple(self.read(s)
                     for s in self.sentences(' '.join(step.claim)))

    # --- rendering ----------------------------------------------------------

    def render(self, rpn):
        """A term written the way a Metamath file writes it."""
        return render(rpn, self.sigs)

    # --- the methods --------------------------------------------------------

    def obtain(self, step, number, scope, facts, lines, closers):
        """Names introduced from an existence claim, which opens a scope.

        This is the step that changes the shape of every step after it. The
        kernel cannot hand a name out of an existential, so everything below
        is proved as the body of an implication and the existential is
        discharged at the very end.

        The claim may come from a definition unfolded, or from a theorem that
        states one outright, and it may introduce more than one name at once:
        `thm:lowest-terms` gives a numerator and a denominator together."""
        got = [n.strip() for n in re.match(
            r'obtain\s+(.+?)(?::|\s+from\b)', step.just.text).group(1)
            .split(',')]
        # Spelt as `parse.NAME` spells an item and not as a run of anything
        # that is not a space: an obtain writing no instantiation puts a
        # comma straight after the name, and it is not part of it.
        named = re.search(rf'\b((?:def|thm):{NAME})', step.just.text)
        saved = dict(self.names)
        if named is None:
            # The line already claims the existence, so there is no item to
            # instantiate and nothing of its own to rename. `SYNTAX.md` says
            # to prefer this form, because the other writes a name into a
            # claim standing above the justification that introduces it,
            # which is the one place in this language where a name is used
            # before the line that names it.
            where = step.just.refs[0] if step.just.refs else None
            held = lines.get(where) if where else None
            if held is None:
                raise Problem('', step.line,
                              'an obtain that names neither an item nor a '
                              'line claiming the existence')
            ex, p_ex = held.term, self.carried(where, facts, lines)
        elif named.group(1).startswith('def:'):
            cites = step.just.text.split(':', 1)[1].strip()
            subject = self.names[instantiation(cites)[0][1]]
            # A fresh name, not the lemma's own: `divides` binds `n`, and a
            # proof that obtains from it twice would introduce one variable
            # for two different numbers.
            lemma, var, kernel, _t, over, left = self.definition(
                named.group(1), subject, var=self.spare_var())
            body = self.term(kernel)
            self.names = saved
            ex = seq(body, var, over, 'wrex')
            p_ex = seq(scope, left, ex, facts[left],
                       self.unfolding(step, lemma, left, ex, var, over, scope,
                                      facts)[0],
                       'mpbid')
        else:
            cites = step.just.text.split(':', 1)[1].strip()
            item = self.items[named.group(1).split(':', 1)[1]]
            for name, value in instantiation(cites):
                self.names[name] = self.term(self.read(value))
            for name in got:
                self.names[name] = f'{self.flabel[name]} cv'
            ex = self.term(self.read(item.conclusions[0][0]))
            self.names = saved
            # An item states its existential in its own names, and a binder
            # takes the variable its name is spelled with. The primes proof
            # obtains a p and concludes that there is a p, so the one it
            # obtains is renamed to a variable nothing else is holding.
            ex = self.renamed(ex, len(got))
            p_ex = self.cite_item(step, ex, scope, facts, item, cites)

        # The existential says which names it introduces and where they run,
        # so the scope is read off it rather than off the text.
        layers, rest = [], self.to_term(ex)
        while len(layers) < len(got):
            body_term, variable, over_term = rest.children
            layers.append((variable.rpn(self.flabel),
                           over_term.rpn(self.flabel)))
            rest = body_term
        body = rest.rpn(self.flabel)

        member = seq(*(seq(f'{v} cv', s, 'wcel') for v, s in layers))
        if len(layers) > 1:
            member = seq(member, 'wa')
        outer, held = self.widen(scope, facts, member)
        inner, lifted = self.widen(outer, held, body)

        for name, (variable, over_term) in zip(got, layers, strict=True):
            self.names[name] = f'{variable} cv'
            self.sets[name] = over_term
        # Read after the obtained names are bound, so a sentence naming one
        # of them is about the variable the existential introduced.
        lines[number] = Fact(body, lifted[body], self.said(step))

        discharge = 'rexlimdva' if len(layers) == 1 else 'rexlimdvva'
        pushed = [v for v, _s in layers] + [s for _v, s in layers]

        def close(proof, goal):
            return seq(scope, ex, goal, p_ex,
                       seq(scope, body, goal, *pushed,
                           seq(outer, body, goal, proof, 'ex'), discharge),
                       'mpd')

        return inner, lifted, [*closers, close]

    def renamed(self, ex, depth):
        """An existential rewritten to bind variables nothing else holds."""
        whole, term, binding = self.to_term(ex), self.to_term(ex), {}
        for _ in range(depth):
            if term.label != 'wrex':
                break
            fresh = self.spare_var()
            binding[term.children[1].variable] = kernel.Term(
                variable=self.sigs[fresh].statement[1])
            term = term.children[0]
        return whole.substitute(binding).rpn(self.flabel)

    def cite_item(self, step, goal, scope, facts, item, cites=None):
        """What an item states, however the database says it is supplied.

        An item with no target is assumed: nothing in the library has its
        shape, and the file says so at its head. An item that has one and
        whose every clause misses is a different thing, and is an error.
        The field says where the claim lands, and it does not land there.

        Assuming it instead would give the same file, the same assumption
        count and no message, so a target that can never fire would read
        exactly like a target nobody wrote."""
        labels = targets.clauses(item)
        for label in labels:
            found = self.apply_lemma(label, self.to_term(goal), scope, facts,
                                     step)
            if found is not None:
                return found
        if labels:
            # `step.just.head` is the word `obtain` here rather than the item,
            # so the item names itself, and the labels it named say which
            # field to go and look at.
            kind = 'def' if item.kind == 'definition' else 'thm'
            raise Problem('', step.line,
                          f'{kind}:{item.name} targets {", ".join(labels)}, '
                          f'and none of them reaches what step '
                          f'{fmt(step.number)} obtains')
        return self.assume_item(step, goal, scope, facts, item, cites)

    def assume_item(self, step, goal, scope, facts, item, cites=None):
        """An item the database gives no target for, taken as it states itself.

        `thm:lowest-terms` is the case: set.mm has nothing of its shape, as
        `db/items.records` says, so what it claims is assumed under the hypotheses
        it asks for."""
        saved = dict(self.names)
        for name, value in instantiation(cites or step.just.text):
            self.names[name] = self.term(self.read(value))
        asks = []
        for kind, text, _label, _line in item.hypotheses:
            body = hypothesis_body(kind, text)
            asks.append(self.term(self.read(body)))
        self.names = saved

        statement = goal
        for one in reversed(asks):
            statement = seq(one, statement, 'wi')
        label = self.fresh('itm')
        text = '|- ' + self.render(statement)
        self.axioms.append((label, text))
        free = sorted({t for t in text.split() if t in self.flabel},
                      key=lambda v: self.forder[self.flabel[v]])
        self.sigs[label] = Signature(
            label, '$a', text.split(),
            [(self.sigs[self.flabel[v]].statement[0], v) for v in free])
        proof = seq(*(self.flabel[v] for v in free), label)
        if not asks:
            return seq(goal, scope, proof, 'a1i')
        for i, one in enumerate(asks):
            rest = goal
            for later in reversed(asks[i + 1:]):
                rest = seq(later, rest, 'wi')
            proof = seq(scope, one, rest,
                        self.settle(self.to_term(one), scope, facts), proof,
                        'syl' if i == 0 else 'mpd')
        return proof

    def carried(self, cite, facts, lines):
        """A cited line's proof, said where the citing step sits.

        A line proved before a block opened holds inside it too, and the
        scope carries a copy that says so. The line's own proof states it at
        the scope it was made in, which is not where a step inside the block
        can use it."""
        held = lines[cite]
        return facts.get(held.term, held.proof)

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
        the body rather than taken from anywhere."""
        where = step.just.target
        held = lines.get(where)
        if held is None:
            raise Problem('', step.line,
                          f'instantiate names no line or label {where!r}')
        # A line may say several things at once, and the `for every` is
        # rarely the first of them: Bezout's line 15 says four and
        # quantifies in the fourth. Unpacking makes each a fact of its own.
        known = dict(facts)
        known[held.term] = self.carried(where, facts, lines)
        self.unpack(held.term, known[held.term], scope, known)
        said = next((p for p in self.parts(held.term)
                     if self.to_term(p).label in ('wral', 'wal')), None)
        if said is None:
            raise Problem('', step.line,
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
                raise Problem('', step.line,
                              'more names instantiated than are quantified')
            mark, at = f'{variable.rpn(self.flabel)} cv', \
                self.term(self.read(value))
            instance = self.restated(body, mark, at)
            ph, ps = body.rpn(self.flabel), instance.rpn(self.flabel)
            member = seq(at, domain, 'wcel')
            asked = self.prove_essential(
                self.to_term(seq(seq(mark, at, 'wceq'),
                                 seq(ph, ps, 'wb'), 'wi')), scope, facts)
            applied = self.ap(lemma, {
                'ph': ph, 'ps': ps, 'x': variable.rpn(self.flabel),
                'A': at, slot: domain}, asked)
            proof = seq(scope, whole.rpn(self.flabel), ps, proof,
                        seq(scope, member,
                            seq(whole.rpn(self.flabel), ps, 'wi'),
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
                raise Problem('', step.line,
                              f'{where} at those terms says '
                              f'{self.render(reached)}, and the step claims '
                              f'{self.render(term)}')
            asks, rest = (c.rpn(self.flabel) for c in reads.children)
            proof = seq(scope, asks, rest,
                        self.settle(self.to_term(asks), scope, facts),
                        proof, 'mpd')
            reached = rest
        return proof

    def substitute(self, step, node, term, scope, facts, lines):
        """One equation put into one claim, at the place the tree names.

        The claim rewritten is the step's own unless the line says otherwise:
        `into line 1` points the congruence at a line already proved, which
        is `ELABORATION.md` requirement 11. The two differ in what comes out —
        rewriting inside a claim gives an equation between the two readings,
        rewriting a whole claim gives a biconditional — so what closes them
        differs too."""
        # The reference is a bracket near the end; the equation may hold
        # brackets of its own, as `S(k) = k(k + 1)/2` does, and `into` may
        # follow, as `substitute √2 = p/q (line 3.1) into line 1` does.
        # A direction is not part of what the line says, so a line that
        # writes one is read the same as a line that does not. `GRAMMAR.md`
        # allows the marker because it tells a reader which way the author
        # had in mind.
        text = re.sub(r',\s*right to left\s*$', '', step.just.text).strip()
        said = re.match(r'substitute\s+(.*)\s*\([^()]*\)'
                        r'(?:\s+into\s+(\S.*?))?\s*$', text)
        if said is None:
            raise Problem('', step.line, 'a substitute that names no equation')
        left, right = self.read(said.group(1)).children
        old, new = self.term(left), self.term(right)
        # Which way the equation faces in the kernel is the lemma's choice,
        # not the text's, so either is accepted and turned if it has to be.
        facing = facts.get(seq(old, new, 'wceq'))
        if facing is None:
            held = facts.get(seq(new, old, 'wceq'))
            if held is None:
                raise Problem('', step.line,
                              f'no equation {old} = {new} in scope')
            facing = seq(scope, new, old, held, 'eqcomd')
        turned = seq(scope, old, new, facing, 'eqcomd')

        if said.group(2) is None:
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
                    try:
                        built, proof = self.rewrite(start, was, now, scope,
                                                    faces)
                    except Problem:
                        continue
                    if built != self.term(other):
                        continue
                    return seq(scope, self.term(start), self.term(other),
                               proof, 'eqcomd') if flip else proof
            raise Problem('', step.line,
                          'the substitution misses the claim')

        where = said.group(2).split()[-1]
        into = lines[where]
        if not into.sentences:
            raise Problem('', step.line,
                          f'{said.group(2)} is not a line to rewrite')
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
                try:
                    built, proof = self.rewrite(one, was, now, scope, faces)
                except Problem:
                    continue
                if built == term:
                    return seq(scope, start, term, known[start], proof,
                               'mpbid')
        raise Problem('', step.line, 'the substitution misses the claim')

    def algebra(self, step, node, term, scope, facts, lines):
        """Decided by `parley/field.py`, then proved by `parley/normal.py`.

        A step that is not an identity of the field is refused rather than
        assumed. One that is gets a proof where `normal.py` can build one:
        both sides are driven to the same canonical term and the step is
        the two of them meeting. What that module does not yet write — a
        quotient, a coefficient past one digit — is taken as stated, which
        is what every `algebra` step was before it existed."""
        self.decide_field(step, term, lines)
        try:
            return self.prove_field(step, term, scope, facts, lines)
        except (normal.Unhandled, Problem) as said:
            if not declined(said):
                raise
            return self.assume(step, term, scope, facts, 'alg', lines)

    def prove_field(self, step, term, scope, facts, lines):
        """An `algebra` claim, by whichever of two routes reaches it."""
        goal = self.to_term(term)
        apart = (goal.variable is None and goal.label == 'wn'
                 and len(goal.children) == 1)
        if not apart and (goal.variable is not None or goal.label != 'wceq'
                          or len(goal.children) != 2):
            raise normal.Unhandled('the claim is not an equation')

        # A `requires` line is where a step says its denominator is not
        # zero, so what the normalizer is asked is asked of those as well
        # as of the scope.
        facts = self.supplied(step, scope, facts) if step is not None \
            else facts

        def complex_number(said):
            """What `normal.py` asks of a subterm it does not look inside."""
            want = seq(said, 'cc', 'wcel')
            if want in facts:
                return facts[want]
            return self.settle(self.to_term(want), scope, facts)

        work = normal.Emitter(self.sigs, scope, complex_number,
                              self.not_zero(scope, facts))
        if apart:
            return self.apart_from_cited(step, goal, scope, facts, lines,
                                         work, complex_number)
        left = goal.children[0].rpn(self.flabel)
        right = goal.children[1].rpn(self.flabel)
        # The routes, in the order they cost, and what each said when it
        # declined. Nested `try`s kept only the last of those, so the step
        # was refused in the words of whichever route happened to be tried
        # last rather than of the one that came nearest.
        routes = [lambda: self.same_polynomial(work, left, right)]
        if step is not None:
            routes += [
                lambda: self.scaled_from_cited(step, left, right, scope,
                                               facts, lines, work),
                lambda: self.crossed_from_cited(step, left, right, scope,
                                                facts, lines, work),
                lambda: self.summed_from_cited(step, left, right, scope,
                                               facts, lines, work)]
        declines = []
        for route in routes:
            try:
                return route()
            except normal.Unhandled as said:
                declines.append(str(said))
        raise normal.Unhandled('; '.join(declines))

    def apart_from_cited(self, step, goal, scope, facts, lines, work,
                         complex_number):
        """A disequality that is a cited one rescaled.

        What the claim says does not vanish is what a cited disequality says
        does not vanish, scaled. So the cited fact becomes a difference that
        is not zero, the two differences are shown to be one polynomial, and
        the claim's difference is not zero either. `subeq0` is what carries a
        difference being zero to the two sides being equal, in both
        directions and under both negations.

        The scalar is 1 or −1. `decide_field` allows any nonzero rational and
        a step wanting another is refused here rather than guessed at: it
        would have to be spelt as a term and multiplied in, and the corpus
        has no such step to check that against."""
        if step is None:
            raise normal.Unhandled('a disequality needs the step it cites')
        claim = field.denied(goal, self.flabel)
        left, right = goal.children[0].children
        lhs, rhs = left.rpn(self.flabel), right.rpn(self.flabel)
        whole = seq(lhs, rhs, 'cmin', 'co')
        for ref in step.just.refs:
            held = lines.get(ref)
            if held is None:
                continue
            for said in self.parts(held.term):
                node = self.to_term(said)
                cited = field.denied(node, self.flabel)
                if cited is None or rescales(cited, claim) not in (1, -1):
                    continue
                p, q = (c.rpn(self.flabel)
                        for c in node.children[0].children)
                gap = seq(p, q, 'cmin', 'co')
                apart = work.ap(
                    'subne0d', {'ph': scope, 'A': p, 'B': q},
                    complex_number(p), complex_number(q),
                    work.ap('neqned', {'ph': scope, 'A': p, 'B': q},
                            self.cited_fact(ref, node, scope, facts, lines)))
                if rescales(cited, claim) == -1:
                    apart = work.ap('negne0d', {'ph': scope, 'A': gap},
                                    complex_number(gap), apart)
                    gap = seq(gap, 'cneg')
                return work.ap(
                    'neneqd', {'ph': scope, 'A': lhs, 'B': rhs},
                    work.ap(
                        'subne0ad', {'ph': scope, 'A': lhs, 'B': rhs},
                        complex_number(lhs), complex_number(rhs),
                        work.ap('eqnetrrd',
                                {'ph': scope, 'A': gap, 'B': whole,
                                 'C': 'cc0'},
                                self.same_polynomial(work, gap, whole),
                                apart)))
        raise normal.Unhandled('no cited disequality is the claim rescaled')

    def crossed_from_cited(self, step, left, right, scope, facts, lines,
                           work):
        """A claim the cited equation already is, once its division goes.

        sqrt2-irrational concludes `m^2 = 2 j^2` from `( m / j ) ^ 2 = 2`.
        Those are the same equation: the second divides where the first
        has multiplied out, and `divmuleq` is the step between them."""
        want = field.equation(self.to_term(seq(left, right, 'wceq')),
                              self.flabel)
        for ref in step.just.refs:
            held = lines.get(ref)
            if held is None:
                continue
            cited = self.to_term(held.term)
            if cited.variable is not None or cited.label != 'wceq' \
                    or len(cited.children) != 2:
                continue
            mine = field.equation(cited, self.flabel)
            if want is None or mine is None or mine.terms != want.terms:
                continue
            try:
                return self.cleared(work, cited, left, right,
                                    self.cited_fact(ref, cited, scope,
                                                    facts, lines))
            except normal.Unhandled:
                continue
        raise normal.Unhandled('no cited equation is the claim divided')

    def cleared(self, work, cited, left, right, given):
        """The cited equation with its denominators multiplied out."""
        was = [one.rpn(self.flabel) for one in cited.children]
        over, under, first = work.as_quotient(
            *work.normalize_quotient(cited.children[0], self.flabel), was[0])
        below, beneath, second = work.as_quotient(
            *work.normalize_quotient(cited.children[1], self.flabel), was[1])
        a, b = work.spell_run(over), work.spell_run(under)
        c, d = work.spell_run(below), work.spell_run(beneath)
        crossed = work.ap(
            'mpbid', {'ph': work.under,
                      'ps': seq(seq(a, b, 'cdiv', 'co'),
                                seq(c, d, 'cdiv', 'co'), 'wceq'),
                      'ch': seq(seq(a, d, 'cmul', 'co'),
                                seq(c, b, 'cmul', 'co'), 'wceq')},
            work.ap('3eqtr3d', {'ph': work.under, 'A': was[0], 'B': was[1],
                                'C': seq(a, b, 'cdiv', 'co'),
                                'D': seq(c, d, 'cdiv', 'co')},
                    given, first, second),
            work.ap('syl2anc',
                    {'ph': work.under,
                     'ps': seq(seq(a, 'cc', 'wcel'), seq(c, 'cc', 'wcel'),
                               'wa'),
                     'ch': seq(seq(seq(b, 'cc', 'wcel'),
                                   seq(b, 'cc0', 'wne'), 'wa'),
                               seq(seq(d, 'cc', 'wcel'),
                                   seq(d, 'cc0', 'wne'), 'wa'), 'wa'),
                     'th': seq(seq(seq(a, b, 'cdiv', 'co'),
                                   seq(c, d, 'cdiv', 'co'), 'wceq'),
                               seq(seq(a, d, 'cmul', 'co'),
                                   seq(c, b, 'cmul', 'co'), 'wceq'), 'wb')},
                    work.ap('jca', {'ph': work.under,
                                    'ps': seq(a, 'cc', 'wcel'),
                                    'ch': seq(c, 'cc', 'wcel')},
                            work.run_cc(over), work.run_cc(below)),
                    work.ap('jca', {'ph': work.under,
                                    'ps': seq(seq(b, 'cc', 'wcel'),
                                              seq(b, 'cc0', 'wne'), 'wa'),
                                    'ch': seq(seq(d, 'cc', 'wcel'),
                                              seq(d, 'cc0', 'wne'), 'wa')},
                            work.pair_of(under), work.pair_of(beneath)),
                    work.ap('divmuleq', {'A': a, 'B': c, 'C': b, 'D': d})))
        return work.ap(
            '3eqtr4d', {'ph': work.under, 'A': seq(a, d, 'cmul', 'co'),
                        'B': seq(c, b, 'cmul', 'co'), 'C': left,
                        'D': right},
            crossed,
            self.same_polynomial(work, left, seq(a, d, 'cmul', 'co')),
            self.same_polynomial(work, right, seq(c, b, 'cmul', 'co')))

    def not_zero(self, scope, facts):
        """What says a denominator is not zero, asked of the scope.

        The text writes these: `requires 2 =/= 0` and `requires q =/= 0`
        are what a step dividing by either of them carries, so the fact is
        there to be found rather than to be proved again here."""
        def apart(said):
            want = seq(said, 'cc0', 'wne')
            if want in facts:
                return facts[want]
            denied = seq(seq(said, 'cc0', 'wceq'), 'wn')
            if denied in facts:
                return seq(scope, said, 'cc0', facts[denied], 'neqned')
            found = self.apart_as_written(said, scope, facts)
            if found is not None:
                return found
            return self.settle(self.to_term(want), scope, facts)
        return apart

    def apart_as_written(self, said, scope, facts):
        """The same fact about the same denominator, spelt as the text spells it.

        A step writes `1 − a ≠ 0` and the normalizer asks about the
        polynomial that is, which it writes as −1·a¹ + 1·1. Those are one
        number and the two lookups above compare spellings, so the fact the
        step wrote is there and is missed. What decides is the polynomial,
        and the equation carrying one spelling to the other is the
        normalizer's own: it is what `normalize` returns beside the terms."""
        work = normal.Emitter(
            self.sigs, scope,
            lambda term: facts.get(seq(term, 'cc', 'wcel'))
            or self.settle(self.to_term(seq(term, 'cc', 'wcel')),
                           scope, facts))
        for fact, proof in facts.items():
            tail = fact.split()[-1]
            if tail not in ('wne', 'wn'):
                continue
            node = self.to_term(fact)
            if node.variable is not None:
                continue
            if node.label == 'wn':
                inner = node.children[0]
                if inner.variable is not None or inner.label != 'wceq':
                    continue
                subject, zero = inner.children
                given = seq(scope, subject.rpn(self.flabel), 'cc0', proof,
                            'neqned')
            else:
                subject, zero = node.children
                given = proof
            was = subject.rpn(self.flabel)
            if zero.rpn(self.flabel) != 'cc0' or was == said:
                continue
            try:
                items, same = work.normalize(subject, self.flabel)
            except (normal.Unhandled, Problem):
                continue
            if work.spell_run(items) != said:
                continue
            return work.ap('eqnetrrd',
                           {'ph': scope, 'A': was, 'B': said, 'C': 'cc0'},
                           same, given)
        return None

    def same_polynomial(self, work, left, right):
        """Two terms driven to one canonical form, and so to each other.

        Where either divides, the canonical form is a numerator over a
        denominator, and two of those are the same when the cross product
        of them is — which is `divmuleq`, and leaves a polynomial identity
        for the case above to answer."""
        first_items, first_under, first = work.normalize_quotient(
            self.to_term(left), self.flabel)
        second_items, second_under, second = work.normalize_quotient(
            self.to_term(right), self.flabel)
        if first_under is None and second_under is None:
            if work.spell_run(first_items) != work.spell_run(second_items):
                raise normal.Unhandled('the two are not one polynomial')
            return work.ap('eqtr4d',
                           {'ph': work.under, 'A': left,
                            'B': work.spell_run(first_items), 'C': right},
                           first, second)
        return self.cross_multiplied(work, left, right,
                                     first_items, first_under, first,
                                     second_items, second_under, second)

    def cross_multiplied(self, work, left, right, over, under, first,
                         below, beneath, second):
        """Two quotients equal, because their cross product is."""
        over, under, first = work.as_quotient(over, under, first, left)
        below, beneath, second = work.as_quotient(below, beneath, second,
                                                  right)
        a, b = work.spell_run(over), work.spell_run(under)
        c, d = work.spell_run(below), work.spell_run(beneath)
        crossed = self.same_polynomial(work, seq(a, d, 'cmul', 'co'),
                                       seq(c, b, 'cmul', 'co'))
        return work.ap(
            'eqtr4d', {'ph': work.under, 'A': left,
                       'B': seq(a, b, 'cdiv', 'co'), 'C': right},
            first,
            work.ap('eqtrd', {'ph': work.under, 'A': right,
                              'B': seq(c, d, 'cdiv', 'co'),
                              'C': seq(a, b, 'cdiv', 'co')},
                    second,
                    work.ap('mpbird',
                            {'ph': work.under,
                             'ps': seq(seq(c, d, 'cdiv', 'co'),
                                       seq(a, b, 'cdiv', 'co'), 'wceq'),
                             'ch': seq(seq(c, b, 'cmul', 'co'),
                                       seq(a, d, 'cmul', 'co'), 'wceq')},
                            work.ap('eqcomd',
                                    {'ph': work.under,
                                     'A': seq(a, d, 'cmul', 'co'),
                                     'B': seq(c, b, 'cmul', 'co')}, crossed),
                            work.ap('syl2anc',
                                    {'ph': work.under,
                                     'ps': seq(seq(c, 'cc', 'wcel'),
                                               seq(a, 'cc', 'wcel'), 'wa'),
                                     'ch': seq(seq(seq(d, 'cc', 'wcel'),
                                                   seq(d, 'cc0', 'wne'),
                                                   'wa'),
                                               seq(seq(b, 'cc', 'wcel'),
                                                   seq(b, 'cc0', 'wne'),
                                                   'wa'), 'wa'),
                                     'th': seq(seq(seq(c, d, 'cdiv', 'co'),
                                                   seq(a, b, 'cdiv', 'co'),
                                                   'wceq'),
                                               seq(seq(c, b, 'cmul', 'co'),
                                                   seq(a, d, 'cmul', 'co'),
                                                   'wceq'), 'wb')},
                                    work.ap('jca',
                                            {'ph': work.under,
                                             'ps': seq(c, 'cc', 'wcel'),
                                             'ch': seq(a, 'cc', 'wcel')},
                                            work.run_cc(below),
                                            work.run_cc(over)),
                                    work.ap('jca',
                                            {'ph': work.under,
                                             'ps': seq(seq(d, 'cc', 'wcel'),
                                                       seq(d, 'cc0', 'wne'),
                                                       'wa'),
                                             'ch': seq(seq(b, 'cc', 'wcel'),
                                                       seq(b, 'cc0', 'wne'),
                                                       'wa')},
                                            work.pair_of(beneath),
                                            work.pair_of(under)),
                                    work.ap('divmuleq',
                                            {'A': c, 'B': a, 'C': d,
                                             'D': b})))))

    def summed_from_cited(self, step, left, right, scope, facts, lines, work):
        """A claim the cited equations add up to.

        Bezout's step 3 takes three at once — `c = q·d + r`, `c = a·u + b·v`
        and `d = a·x₀ + b·y₀` — at −1, 1 and −q, and is the only step in the
        corpus whose multipliers are not all constants. `decide_field` works
        those out to decide the step at all and hands them over; what is
        left is saying it. Each cited equation is a difference that is zero;
        each is multiplied by what the combination says, and stays zero; the
        sum of them is zero because every one is; and that sum is the
        claim's own difference, which is the normalizer's question."""
        want = field.equation(self.to_term(seq(left, right, 'wceq')),
                              self.flabel)
        given, where = [], []
        for ref in step.just.refs:
            held = lines.get(ref)
            if held is None:
                continue
            for said in self.parts(held.term):
                node = self.to_term(said)
                one = field.equation(node, self.flabel)
                if one is not None:
                    given.append(one)
                    where.append((ref, node))
        if want is None or not given:
            raise normal.Unhandled('the step cites no equation')

        def in_cc(said):
            """( scope -> said e. CC ), for a term of the step's own depth.

            The claim's sides are as deep as the step wrote them — Bezout's
            is a sum of two products of a difference of a product — and each
            level is a closure lemma with the atoms at the bottom reached
            through `recn`. Five is not enough for that and is the depth a
            side condition wants, so this asks for its own."""
            want_cc = seq(said, 'cc', 'wcel')
            if want_cc in facts:
                return facts[want_cc]
            return self.settle(self.to_term(want_cc), scope, facts, depth=12)

        atoms = {a for p in [*given, want] for m in p.terms for a, _ in m}
        how = field.follows(given, want, atoms)
        if not how:
            raise normal.Unhandled('no sum of the cited equations is the '
                                   'claim')
        pieces = []
        for which, shape, scale in how:
            ref, node = where[which]
            a, b = (c.rpn(self.flabel) for c in node.children)
            gap = seq(a, b, 'cmin', 'co')
            times = multiplier(shape, scale)
            if times is None:
                raise normal.Unhandled('a multiplier with no spelling')
            vanishes = work.ap(
                'mpbird', {'ph': scope, 'ps': seq(gap, 'cc0', 'wceq'),
                           'ch': seq(a, b, 'wceq')},
                self.cited_fact(ref, node, scope, facts, lines),
                work.ap('subeq0ad', {'ph': scope, 'A': a, 'B': b},
                        in_cc(a), in_cc(b)))
            piece = seq(times, gap, 'cmul', 'co')
            pieces.append((piece, work.ap(
                'eqtrd', {'ph': scope, 'A': piece,
                          'B': seq(times, 'cc0', 'cmul', 'co'), 'C': 'cc0'},
                work.ap('oveq2d', {'ph': scope, 'A': gap, 'B': 'cc0',
                                   'C': times, 'F': 'cmul'}, vanishes),
                work.ap('mul01d', {'ph': scope, 'A': times},
                        work.atom(times)))))
        total, sums = pieces[0]
        for piece, proof in pieces[1:]:
            joined = seq(total, piece, 'caddc', 'co')
            sums = work.ap(
                'eqtrd', {'ph': scope, 'A': joined,
                          'B': seq('cc0', 'cc0', 'caddc', 'co'), 'C': 'cc0'},
                work.ap('oveq12d',
                        {'ph': scope, 'A': total, 'B': 'cc0', 'C': piece,
                         'D': 'cc0', 'F': 'caddc'}, sums, proof),
                work.a1i(seq(seq('cc0', 'cc0', 'caddc', 'co'), 'cc0',
                             'wceq'), '00id'))
            total = joined
        whole = seq(left, right, 'cmin', 'co')
        return work.ap(
            'mpbid', {'ph': scope, 'ps': seq(whole, 'cc0', 'wceq'),
                      'ch': seq(left, right, 'wceq')},
            work.ap('eqtr3d',
                    {'ph': scope, 'A': total, 'B': whole, 'C': 'cc0'},
                    self.same_polynomial(work, total, whole), sums),
            work.ap('subeq0ad', {'ph': scope, 'A': left, 'B': right},
                    in_cc(left), in_cc(right)))

    def scaled_from_cited(self, step, left, right, scope, facts, lines, work):
        """A claim a cited equation is a whole multiple of.

        sqrt2-irrational concludes `j^2 = 2 p^2` from `2 j^2 = 4 p^2`: the
        equation it cites is the claim with both sides doubled. Proving
        each side is that multiple is the polynomial case again, and what
        is left is cancelling the multiplier."""
        want = field.equation(self.to_term(seq(left, right, 'wceq')),
                              self.flabel)
        for ref in step.just.refs:
            held = lines.get(ref)
            if held is None:
                continue
            cited = self.to_term(held.term)
            if cited.variable is not None or cited.label != 'wceq':
                continue
            times = whole_multiple(
                field.equation(cited, self.flabel), want)
            if times is None or f'{times}ne0' not in self.sigs:
                continue
            scaled = [seq(field.NUMERAL[times], one, 'cmul', 'co')
                      for one in (left, right)]
            try:
                sides = [self.same_polynomial(work, was, now) for was, now
                         in zip([c.rpn(self.flabel) for c in cited.children],
                                scaled, strict=True)]
            except normal.Unhandled:
                continue
            return self.cancel_multiple(work, times, left, right, scaled,
                                        sides, self.carried(ref, facts,
                                                            lines),
                                        cited, scope, facts)
        raise normal.Unhandled('no cited equation is a multiple of the claim')

    def cancel_multiple(self, work, times, left, right, scaled, sides,
                        given, cited, scope, facts):
        """The multiplier taken off both sides, which is `mulcan`."""
        numeral = field.NUMERAL[times]
        matched = work.ap(
            '3eqtr3d', {'ph': scope, 'A': cited.children[0].rpn(self.flabel),
                        'B': cited.children[1].rpn(self.flabel),
                        'C': scaled[0], 'D': scaled[1]},
            given, *sides)
        return work.ap(
            'mpbid', {'ph': scope, 'ps': seq(scaled[0], scaled[1], 'wceq'),
                      'ch': seq(left, right, 'wceq')},
            matched,
            work.ap('syl3anc',
                    {'ph': scope, 'ps': seq(left, 'cc', 'wcel'),
                     'ch': seq(right, 'cc', 'wcel'),
                     'th': seq(seq(numeral, 'cc', 'wcel'),
                               seq(numeral, 'cc0', 'wne'), 'wa'),
                     'ta': seq(seq(scaled[0], scaled[1], 'wceq'),
                               seq(left, right, 'wceq'), 'wb')},
                    self.settle(self.to_term(seq(left, 'cc', 'wcel')),
                                scope, facts),
                    self.settle(self.to_term(seq(right, 'cc', 'wcel')),
                                scope, facts),
                    work.ap('jca', {'ph': scope,
                                    'ps': seq(numeral, 'cc', 'wcel'),
                                    'ch': seq(numeral, 'cc0', 'wne')},
                            work.number(times),
                            work.a1i(seq(numeral, 'cc0', 'wne'),
                                     f'{times}ne0')),
                    work.ap('mulcan', {'A': left, 'B': right,
                                       'C': numeral})))

    def decide_field(self, step, term, lines):
        """Refuse an `algebra` step that is not an identity.

        With nothing cited the claim must vanish outright; with equations
        cited it must be a combination of them. That the denominators are
        not zero is not decided here — the text writes those as `requires`
        lines, which is what `METHODS.md` means by them being hypotheses of
        the method."""
        claim = field.equation(self.to_term(term), self.flabel)
        if claim is None:
            return self.decide_apart(step, term, lines)
        given = []
        for ref in step.just.refs:
            held = lines.get(ref)
            if held is None:
                continue
            for said in self.parts(held.term):
                one = field.equation(self.to_term(said), self.flabel)
                if one is not None:
                    given.append(one)
        atoms = {a for p in [*given, claim] for m in p.terms for a, _ in m}
        if field.follows(given, claim, atoms) is None:
            raise Problem('', step.line,
                          f'{self.render(term)} is not an identity, nor does '
                          f'it follow from what step {fmt(step.number)} '
                          f'cites')

    def decide_apart(self, step, term, lines):
        """Refuse a disequality `algebra` step that is not a cited one rescaled.

        This method is allowed one disequality and no more: the claim holds
        when what it says does not vanish is a nonzero multiple of what a
        cited disequality says does not vanish. Anything else is a fact
        about the field rather than an identity of it — that a² is not zero
        when a is not needs the field to have no zero divisors, and nothing
        here decides that.

        A claim that is neither an equation nor a disequality is left alone,
        as it was before either was decided."""
        claim = field.denied(self.to_term(term), self.flabel)
        if claim is None:
            return
        for ref in step.just.refs:
            held = lines.get(ref)
            if held is None:
                continue
            for said in self.parts(held.term):
                one = field.denied(self.to_term(said), self.flabel)
                if one is not None and rescales(one, claim) is not None:
                    return
        raise Problem('', step.line,
                      f'{self.render(term)} is not a rescaling of any '
                      f'disequality step {fmt(step.number)} cites')

    def arithmetic(self, step, node, term, scope, facts, lines):
        """Closed numerals, worked out and then said. `METHODS.md`.

        A relation between two numerals is said outright; a value is an
        identity of the field with no atoms in it, so it goes where
        identities go rather than wanting a second procedure."""
        for how in (lambda: self.prove_numeral(term, scope, facts),
                    lambda: self.prove_field(step, term, scope, facts,
                                             lines)):
            try:
                return how()
            except (normal.Unhandled, Problem) as said:
                if not declined(said):
                    raise
                continue
        return self.assume(step, term, scope, facts, 'ari', lines)

    def prove_numeral(self, term, scope, facts):
        """A closed numeral fact, decided by working it out and then said.

        What `arithmetic` takes is closed, so deciding is arithmetic on two
        whole numbers and needs no procedure. Saying it rests on one thing
        set.mm names for every pair — that one number is below another —
        and everything else is that weakened or turned: `ltle` for `at
        most`, `ltne` for `not equal`, `leid` and `eqid` where the two are
        the same number."""
        goal = self.to_term(term)
        negated = False
        if goal.variable is None and goal.label == 'wn' \
                and len(goal.children) == 1:
            negated, goal = True, goal.children[0]
        sides = order_sides(goal)
        if sides is None:
            raise normal.Unhandled('the claim states no relation')
        first, second = (linear.numeral(one, self.flabel)
                         for one in sides[:2])
        if first is None or second is None \
                or first.denominator != 1 or second.denominator != 1 \
                or not all(0 <= int(n) <= 9 for n in (first, second)):
            raise normal.Unhandled('the two sides are not single digits')
        # Each side must *be* its digit, not merely come to it. What set.mm
        # names is a fact about the digits, so a side that works out to one
        # without being written as one is a computation, and this is not
        # the method that does computations.
        if any(one.rpn(self.flabel) != field.NUMERAL[int(value)]
               for one, value in zip(sides[:2], (first, second),
                                     strict=True)):
            raise normal.Unhandled('a side works out to a digit but is one '
                                   'only after working out')
        a, b, how = int(first), int(second), sides[2]
        work = normal.Emitter(self.sigs, scope,
                              lambda t: self.settle(
                                  self.to_term(seq(t, 'cc', 'wcel')),
                                  scope, facts))
        if negated:
            if how != '=' or a == b:
                raise normal.Unhandled('a denial of what holds')
            return self.numerals_differ(work, a, b)
        if how == '=' and a == b:
            return work.a1i(seq(field.NUMERAL[a], field.NUMERAL[b], 'wceq'),
                            work.ap('eqid', {'A': field.NUMERAL[a]}))
        if how == '<' and a < b:
            return self.numeral_below(work, a, b)
        if how == '<=' and a <= b:
            if a == b:
                return work.ap(
                    'syl', {'ph': scope,
                            'ps': seq(field.NUMERAL[a], 'cr', 'wcel'),
                            'ch': seq(field.NUMERAL[a], field.NUMERAL[a],
                                      'cle', 'wbr')},
                    self.numeral_real(work, a),
                    work.ap('leid', {'A': field.NUMERAL[a]}))
            return work.ap(
                'mpd', {'ph': scope,
                        'ps': seq(field.NUMERAL[a], field.NUMERAL[b], 'clt',
                                  'wbr'),
                        'ch': seq(field.NUMERAL[a], field.NUMERAL[b], 'cle',
                                  'wbr')},
                self.numeral_below(work, a, b),
                work.ap('syl2anc',
                        {'ph': scope,
                         'ps': seq(field.NUMERAL[a], 'cr', 'wcel'),
                         'ch': seq(field.NUMERAL[b], 'cr', 'wcel'),
                         'th': seq(seq(field.NUMERAL[a], field.NUMERAL[b],
                                       'clt', 'wbr'),
                                   seq(field.NUMERAL[a], field.NUMERAL[b],
                                       'cle', 'wbr'), 'wi')},
                        self.numeral_real(work, a),
                        self.numeral_real(work, b),
                        work.ap('ltle', {'A': field.NUMERAL[a],
                                         'B': field.NUMERAL[b]})))
        raise normal.Unhandled(f'{a} {how} {b} is not what the numbers do')

    def numeral_real(self, work, value):
        return work.a1i(seq(field.NUMERAL[value], 'cr', 'wcel'),
                        f'{value}re')

    def numeral_below(self, work, a, b):
        """( scope -> a < b ), the one thing set.mm names for every pair.

        It names `0 < n` as `npos` rather than `0ltn`, and one is the
        exception to that, so the three spellings are all there is."""
        if a != 0:
            label = f'{a}lt{b}'
        else:
            label = '0lt1' if b == 1 else f'{b}pos'
        return work.a1i(seq(field.NUMERAL[a], field.NUMERAL[b], 'clt',
                            'wbr'), label)

    def numerals_differ(self, work, a, b):
        """( scope -> -. a = b ), from whichever of the two is below."""
        low, high = (a, b) if a < b else (b, a)
        apart = work.ap(
            'syl', {'ph': work.under,
                    'ps': seq(seq(field.NUMERAL[low], 'cr', 'wcel'),
                              seq(field.NUMERAL[low], field.NUMERAL[high],
                                  'clt', 'wbr'), 'wa'),
                    'ch': seq(field.NUMERAL[high], field.NUMERAL[low],
                              'wne')},
            work.ap('jca', {'ph': work.under,
                            'ps': seq(field.NUMERAL[low], 'cr', 'wcel'),
                            'ch': seq(field.NUMERAL[low],
                                      field.NUMERAL[high], 'clt', 'wbr')},
                    self.numeral_real(work, low),
                    self.numeral_below(work, low, high)),
            work.ap('ltne', {'A': field.NUMERAL[low],
                             'B': field.NUMERAL[high]}))
        if a != low:
            return work.ap('neneqd', {'ph': work.under,
                                      'A': field.NUMERAL[a],
                                      'B': field.NUMERAL[b]}, apart)
        return work.ap(
            'neneqd', {'ph': work.under, 'A': field.NUMERAL[a],
                       'B': field.NUMERAL[b]},
            work.ap('necomd', {'ph': work.under, 'A': field.NUMERAL[high],
                               'B': field.NUMERAL[low]}, apart))

    def inequalities(self, step, node, term, scope, facts, lines):
        """Decided by `parley/linear.py`, and then taken.

        The decision is not the proof. What the method concludes is checked
        against what the step cites — the claim is denied and the set shown
        to have no solution over an ordered field — so a step that does not
        follow is refused rather than assumed. What is still assumed is the
        step it was allowed to take, which is why the head of the file
        lists it. Emitting the proof of a decided step wants a normal form
        for sums that `algebra` does not have yet.

        A step that cites nothing decidable is taken as before: the method
        carries steps whose facts are not linear, and `METHODS.md` refuses
        those rather than this."""
        self.decide_order(step, term, lines)
        try:
            return self.prove_order(step.just.refs, term, scope, facts,
                                    lines)
        except (normal.Unhandled, Problem) as said:
            if not declined(said):
                raise
            return self.assume(step, term, scope, facts, 'ine', lines)

    def prove_order(self, refs, term, scope, facts, lines, skip=()):
        """An `inequalities` claim, by whichever route reaches it.

        `skip` names sentences of the cited lines to leave out. A case of a
        split is proved by this same method one scope in, and the
        disequality it split on must not be there to split on again.

        What is passed is the lines the claim rests on, not the step, so
        that a `requires` line asking for the method is answered the same
        way a step is: `side` has citations where a step has `from`.

        `linear.certificate` says which cited facts the claim is built
        from and in what multiple. Where the only one used is an equation,
        the claim is that equation times a number: the difference it says
        is zero, scaled, is the difference the claim says is zero, and the
        two being the same expression is a question for the normalizer.

        A combination that scales an inequality is a different proof and
        is not written yet, so those steps stay assumed."""
        goal = self.to_term(term)
        given, where = [], []
        for ref in refs:
            held = lines.get(ref)
            if held is None:
                continue
            for said in self.parts(held.term):
                if said in skip:
                    continue
                one = linear.fact(self.to_term(said), self.flabel)
                if one is not None:
                    given.append(one)
                    where.append((ref, self.to_term(said)))
        claim = linear.fact(goal, self.flabel)
        if claim is None:
            raise normal.Unhandled('the claim is not linear')
        found = linear.certificate([*given, linear.opposite(claim)])
        if not isinstance(found, dict):
            return self.either_way(found, refs, where, given, term, scope,
                                   facts, lines, skip)
        if len(given) not in found:
            # The denied claim went unused, so the cited facts refute each
            # other and the claim holds because nothing does. That is not
            # this method's to emit; a case of a split says so where it
            # supposed the bound that cannot hold.
            raise normal.Unhandled('the cited facts refute each other')
        used = [i for i, k in found.items() if k and i < len(given)]
        weight = found[len(given)]
        if claim.how == '=/=':
            return self.stays_apart(used, given, where, claim, scope, facts,
                                    lines)
        if goal.variable is None and goal.label == 'wn':
            return self.negated_order(goal, refs, term, scope, facts, lines,
                                      skip)
        sides = order_sides(goal)
        if sides is None:
            raise normal.Unhandled('the claim states no relation')
        left, right, how = sides
        left, right = left.rpn(self.flabel), right.rpn(self.flabel)
        if len(used) == 1 and given[used[0]].how == '=':
            return self.from_equation(where[used[0]],
                                      found[used[0]] / weight,
                                      left, right, how, scope, facts, lines)
        # What the scaled facts leave over is a constant, and `METHODS.md`
        # says the method may use a closed numeral fact the step does not
        # cite. It is what makes `n! >_ 1` give `n! + 1 > 1`.
        spare = claim.side
        for i in used:
            spare = spare.minus(given[i].side.scaled(found[i] / weight))
        if not spare.constant_only():
            raise normal.Unhandled('what is left over is not a constant')
        return self.from_sum([(where[i], given[i], found[i] / weight)
                              for i in used],
                             left, right, how, spare.constant, scope, facts,
                             lines)

    def negated_order(self, goal, refs, term, scope, facts, lines, skip):
        """A claim denying a relation, as the relation that holds instead.

        `not ( d ≤ r )` is `r < d`. `linear.fact` has always read it that
        way — `METHODS.md` calls a negation a fact and not a special case —
        and `order_sides` cannot read a denial at all, so such a claim was
        decided and then had nothing to emit. What holds instead is proved
        first, and `ltnle` or `lenlt` turns it round. Those are two of the
        three labels `db/methods.records` names for this method."""
        sides = order_sides(goal.children[0])
        if sides is None or sides[2] not in ('<', '<='):
            raise normal.Unhandled('what is denied states no relation')
        a, b = (one.rpn(self.flabel) for one in sides[:2])
        turns, how = (('ltnle', 'clt') if sides[2] == '<='
                      else ('lenlt', 'cle'))
        instead = seq(b, a, how, 'wbr')
        held = facts.get(instead)
        if held is None:
            held = self.prove_order(refs, instead, scope, facts, lines, skip)

        def real(one):
            want = seq(one, 'cr', 'wcel')
            return facts.get(want) or self.settle(self.to_term(want), scope,
                                                  facts)
        work = normal.Emitter(self.sigs, scope, lambda t: self.settle(
            self.to_term(seq(t, 'cc', 'wcel')), scope, facts))
        return work.ap(
            'mpbid', {'ph': scope, 'ps': instead, 'ch': term}, held,
            work.ap('syl2anc',
                    {'ph': scope, 'ps': seq(b, 'cr', 'wcel'),
                     'ch': seq(a, 'cr', 'wcel'),
                     'th': seq(instead, term, 'wb')},
                    real(b), real(a), work.ap(turns, {'A': b, 'B': a})))

    def either_way(self, found, refs, where, given, term, scope, facts,
                   lines, skip):
        """A claim proved twice, once each side of a cited disequality.

        `a ≠ b` is `a < b or b < a`, so a refutation that uses one has to
        try both, and `linear.certificate` says so by returning no single
        combination. Each side is the same claim at a scope one wider, with
        the side's bound standing as a line of its own, so the method proves
        it the way it proves anything; a side that splits again is another
        of these. `mpjaodan` puts the two back together."""
        _tag, which = found[0], found[1]
        if which >= len(given):
            raise normal.Unhandled('what splits is the claim, not a citation')
        ref, said = where[which]
        if said.variable is not None or said.label != 'wn' \
                or said.children[0].label != 'wceq':
            raise normal.Unhandled('what splits is not a denied equation')
        a, b = (c.rpn(self.flabel) for c in said.children[0].children)
        below, above = (seq(a, b, 'clt', 'wbr'), seq(b, a, 'clt', 'wbr'))

        work = normal.Emitter(self.sigs, scope, lambda t: self.settle(
            self.to_term(seq(t, 'cc', 'wcel')), scope, facts))

        def real(one):
            want = seq(one, 'cr', 'wcel')
            return facts.get(want) or self.settle(self.to_term(want), scope,
                                                  facts)

        whether = work.ap(
            'mpbid', {'ph': scope, 'ps': seq(a, b, 'wne'),
                      'ch': seq(below, above, 'wo')},
            work.ap('neqned', {'ph': scope, 'A': a, 'B': b},
                    self.cited_fact(ref, said, scope, facts, lines)),
            work.ap('syl2anc',
                    {'ph': scope, 'ps': seq(a, 'cr', 'wcel'),
                     'ch': seq(b, 'cr', 'wcel'),
                     'th': seq(seq(a, b, 'wne'),
                               seq(below, above, 'wo'), 'wb')},
                    real(a), real(b), work.ap('lttri2', {'A': a, 'B': b})))

        frame, sides = len(self.frames), []
        for bound in (below, above):
            inner, lifted = self.widen(scope, facts, bound)
            held = dict(lines)
            held[bound] = Fact(bound, lifted[bound])
            sides.append(self.one_way(bound, term, inner, lifted, held,
                                      [*refs, bound],
                                      (*skip, said.rpn(self.flabel))))
        del self.frames[frame:]
        return work.ap('mpjaodan',
                       {'ph': scope, 'ps': below, 'ch': term, 'th': above},
                       sides[0], sides[1], whether)

    def one_way(self, bound, term, scope, facts, lines, refs, skip):
        """One side of a split, at the scope that side opened.

        Three ways, in the order they cost. The side's own bound may be the
        claim. The claim may follow from the bound and what is cited, which
        is the method again. Or the bound may contradict what is cited, and
        then the claim holds because nothing does: the case is impossible
        and `METHODS.md` counts it refuted rather than proved."""
        if term in facts:
            return facts[term]
        try:
            return self.prove_order(refs, term, scope, facts, lines, skip)
        except (normal.Unhandled, Problem):
            pass
        return self.impossible(bound, term, scope, facts)

    def impossible(self, bound, term, scope, facts):
        """The claim, because the bound this scope opened cannot hold.

        `lenlt` is what says so: a ≤ b and b < a deny each other, and the
        step already has the first where the case supposes the second."""
        node = self.to_term(bound)
        sides = order_sides(node)
        if sides is None or sides[2] != '<':
            raise normal.Unhandled('the bound states no strict order')
        low, high = (one.rpn(self.flabel) for one in sides[:2])
        denies = seq(high, low, 'cle', 'wbr')
        if denies not in facts:
            raise normal.Unhandled('nothing in scope denies the bound')

        def real(one):
            want = seq(one, 'cr', 'wcel')
            return facts.get(want) or self.settle(self.to_term(want), scope,
                                                  facts)
        work = normal.Emitter(self.sigs, scope, lambda t: self.settle(
            self.to_term(seq(t, 'cc', 'wcel')), scope, facts))
        return work.ap(
            'pm2.21dd', {'ph': scope, 'ps': bound, 'ch': term},
            facts[bound],
            work.ap('mpbid', {'ph': scope, 'ps': denies,
                              'ch': seq(bound, 'wn')},
                    facts[denies],
                    work.ap('syl2anc',
                            {'ph': scope, 'ps': seq(high, 'cr', 'wcel'),
                             'ch': seq(low, 'cr', 'wcel'),
                             'th': seq(denies, seq(bound, 'wn'), 'wb')},
                            real(high), real(low),
                            work.ap('lenlt', {'A': high, 'B': low}))))

    def stays_apart(self, used, given, where, claim, scope, facts, lines):
        """Two things the step says are not equal, because one is below.

        The claim is a denial, so the combination that reaches it is the
        denial supposed and contradicted. Where the contradiction is with
        a single strict bound between the very two the claim names, that
        whole argument is `ltne`: something below another is not it."""
        if len(used) != 1 or given[used[0]].how != '<':
            raise normal.Unhandled('not one strict bound')
        ref, said = where[used[0]]
        parts = order_sides(said)
        if parts is None or parts[2] != '<':
            raise normal.Unhandled('the cited bound is not stated as one')
        below = [c.rpn(self.flabel) for c in said.children[:2]]
        # The claim must be about the two the bound is about, and no more.
        if claim.side.minus(given[used[0]].side.scaled(-1)).atoms() \
                or claim.side.minus(
                    given[used[0]].side.scaled(-1)).constant:
            raise normal.Unhandled('the claim is not that bound turned')
        work = normal.Emitter(self.sigs, scope,
                              lambda t: self.settle(
                                  self.to_term(seq(t, 'cc', 'wcel')),
                                  scope, facts))

        def real_number(one):
            want = seq(one, 'cr', 'wcel')
            if want in facts:
                return facts[want]
            return self.settle(self.to_term(want), scope, facts)

        return work.ap(
            'neneqd', {'ph': scope, 'A': below[1], 'B': below[0]},
            work.ap('syl2anc',
                    {'ph': scope, 'ps': seq(below[0], 'cr', 'wcel'),
                     'ch': seq(below[0], below[1], 'clt', 'wbr'),
                     'th': seq(below[1], below[0], 'wne')},
                    real_number(below[0]),
                    self.cited_fact(ref, said, scope, facts, lines),
                    work.ap('ltne', {'A': below[0], 'B': below[1]})))

    def from_sum(self, used, left, right, how, spare, scope, facts, lines):
        """The claim as the cited bounds added, and what they leave over.

        Each says a difference is at most zero; added, the two differences
        are the claim's, which is the normalizer's question. `le2add` is
        the addition, and what it lands on is zero plus zero.

        A claim that is strict gets its strictness from the constant the
        bounds leave over, which is a closed numeral fact the step does
        not cite. `METHODS.md` says the method may use one."""
        if how == '<':
            if spare != -1 or len(used) != 1:
                raise normal.Unhandled('only one bound short of one is '
                                       'written')
        elif how != '<=' or spare != 0:
            raise normal.Unhandled('only one or two bounds is written')
        if not 1 <= len(used) <= 2:
            raise normal.Unhandled('only one or two bounds is written')

        def real_number(one):
            want = seq(one, 'cr', 'wcel')
            if want in facts:
                return facts[want]
            return self.settle(self.to_term(want), scope, facts)

        work = normal.Emitter(self.sigs, scope,
                              lambda t: self.settle(
                                  self.to_term(seq(t, 'cc', 'wcel')),
                                  scope, facts))
        gaps, bounds, real = [], [], []
        for (ref, said), fact, times in used:
            one, proof, held = self.at_most_zero(
                work, said, fact, times,
                self.cited_fact(ref, said, scope, facts, lines),
                real_number)
            gaps.append(one)
            bounds.append(proof)
            real.append(held)
        if how == '<':
            return self.short_of_one(work, gaps[0], bounds[0], real[0],
                                     left, right, real_number)
        if len(gaps) == 1:
            # Nothing to add: the one bound is already the claim's.
            return self.bound_reaches(work, gaps[0], bounds[0], left, right,
                                      real_number)
        total = seq(gaps[0], gaps[1], 'caddc', 'co')
        zero = work.a1i(seq('cc0', 'cr', 'wcel'), '0re')
        added = work.ap(
            'breqtrd', {'ph': scope, 'A': total,
                        'B': seq('cc0', 'cc0', 'caddc', 'co'), 'C': 'cc0',
                        'R': 'cle'},
            work.ap('mpd',
                    {'ph': scope,
                     'ps': seq(seq(gaps[0], 'cc0', 'cle', 'wbr'),
                               seq(gaps[1], 'cc0', 'cle', 'wbr'), 'wa'),
                     'ch': seq(total, seq('cc0', 'cc0', 'caddc', 'co'),
                               'cle', 'wbr')},
                    work.ap('jca', {'ph': scope,
                                    'ps': seq(gaps[0], 'cc0', 'cle', 'wbr'),
                                    'ch': seq(gaps[1], 'cc0', 'cle', 'wbr')},
                            *bounds),
                    work.ap('syl',
                            {'ph': scope,
                             'ps': seq(seq(seq(gaps[0], 'cr', 'wcel'),
                                           seq(gaps[1], 'cr', 'wcel'), 'wa'),
                                       seq(seq('cc0', 'cr', 'wcel'),
                                           seq('cc0', 'cr', 'wcel'), 'wa'),
                                       'wa'),
                             'ch': seq(seq(seq(gaps[0], 'cc0', 'cle', 'wbr'),
                                           seq(gaps[1], 'cc0', 'cle', 'wbr'),
                                           'wa'),
                                       seq(total,
                                           seq('cc0', 'cc0', 'caddc', 'co'),
                                           'cle', 'wbr'), 'wi')},
                            work.ap('jca',
                                    {'ph': scope,
                                     'ps': seq(seq(gaps[0], 'cr', 'wcel'),
                                               seq(gaps[1], 'cr', 'wcel'),
                                               'wa'),
                                     'ch': seq(seq('cc0', 'cr', 'wcel'),
                                               seq('cc0', 'cr', 'wcel'),
                                               'wa')},
                                    work.ap('jca',
                                            {'ph': scope,
                                             'ps': seq(gaps[0], 'cr', 'wcel'),
                                             'ch': seq(gaps[1], 'cr',
                                                       'wcel')}, *real),
                                    work.ap('jca',
                                            {'ph': scope,
                                             'ps': seq('cc0', 'cr', 'wcel'),
                                             'ch': seq('cc0', 'cr', 'wcel')},
                                            zero, zero)),
                            work.ap('le2add', {'A': gaps[0], 'B': gaps[1],
                                               'C': 'cc0', 'D': 'cc0'}))),
            work.a1i(seq(seq('cc0', 'cc0', 'caddc', 'co'), 'cc0', 'wceq'),
                     '00id'))
        return self.bound_reaches(work, total, added, left, right,
                                  real_number)

    def short_of_one(self, work, gap, bound, gap_real, left, right,
                     real_number):
        """A bound and a minus one, added, to reach a strict claim.

        `leltadd` is the addition that keeps the strictness, and `suble0`
        has no strict twin, so the claim comes back through `ltsubadd`
        with nothing on the right and `addlid` to tidy it."""
        scope = work.under
        minus, span = seq('c1', 'cneg'), seq(left, right, 'cmin', 'co')
        total = seq(gap, minus, 'caddc', 'co')
        zero = work.a1i(seq('cc0', 'cr', 'wcel'), '0re')
        pair = seq(seq(gap, 'cr', 'wcel'), seq(minus, 'cr', 'wcel'), 'wa')
        added = work.ap(
            'breqtrd', {'ph': scope, 'A': total,
                        'B': seq('cc0', 'cc0', 'caddc', 'co'), 'C': 'cc0',
                        'R': 'clt'},
            work.ap('mpd',
                    {'ph': scope,
                     'ps': seq(seq(gap, 'cc0', 'cle', 'wbr'),
                               seq(minus, 'cc0', 'clt', 'wbr'), 'wa'),
                     'ch': seq(total, seq('cc0', 'cc0', 'caddc', 'co'),
                               'clt', 'wbr')},
                    work.ap('jca', {'ph': scope,
                                    'ps': seq(gap, 'cc0', 'cle', 'wbr'),
                                    'ch': seq(minus, 'cc0', 'clt', 'wbr')},
                            bound,
                            work.a1i(seq(minus, 'cc0', 'clt', 'wbr'),
                                     'neg1lt0')),
                    work.ap('syl',
                            {'ph': scope,
                             'ps': seq(pair,
                                       seq(seq('cc0', 'cr', 'wcel'),
                                           seq('cc0', 'cr', 'wcel'), 'wa'),
                                       'wa'),
                             'ch': seq(seq(seq(gap, 'cc0', 'cle', 'wbr'),
                                           seq(minus, 'cc0', 'clt', 'wbr'),
                                           'wa'),
                                       seq(total,
                                           seq('cc0', 'cc0', 'caddc', 'co'),
                                           'clt', 'wbr'), 'wi')},
                            work.ap('jca',
                                    {'ph': scope, 'ps': pair,
                                     'ch': seq(seq('cc0', 'cr', 'wcel'),
                                               seq('cc0', 'cr', 'wcel'),
                                               'wa')},
                                    work.ap('jca',
                                            {'ph': scope,
                                             'ps': seq(gap, 'cr', 'wcel'),
                                             'ch': seq(minus, 'cr', 'wcel')},
                                            gap_real,
                                            self.real_numeral(
                                                work, Fraction(-1))),
                                    work.ap('jca',
                                            {'ph': scope,
                                             'ps': seq('cc0', 'cr', 'wcel'),
                                             'ch': seq('cc0', 'cr', 'wcel')},
                                            zero, zero)),
                            work.ap('leltadd', {'A': gap, 'B': minus,
                                                'C': 'cc0', 'D': 'cc0'}))),
            work.a1i(seq(seq('cc0', 'cc0', 'caddc', 'co'), 'cc0', 'wceq'),
                     '00id'))
        return work.ap(
            'breqtrd', {'ph': scope, 'A': left,
                        'B': seq('cc0', right, 'caddc', 'co'), 'C': right,
                        'R': 'clt'},
            work.ap('mpbid',
                    {'ph': scope, 'ps': seq(span, 'cc0', 'clt', 'wbr'),
                     'ch': seq(left, seq('cc0', right, 'caddc', 'co'),
                               'clt', 'wbr')},
                    work.ap('eqbrtrd', {'ph': scope, 'A': span, 'B': total,
                                        'C': 'cc0', 'R': 'clt'},
                            self.same_polynomial(work, span, total), added),
                    work.ap('syl3anc',
                            {'ph': scope, 'ps': seq(left, 'cr', 'wcel'),
                             'ch': seq(right, 'cr', 'wcel'),
                             'th': seq('cc0', 'cr', 'wcel'),
                             'ta': seq(seq(span, 'cc0', 'clt', 'wbr'),
                                       seq(left,
                                           seq('cc0', right, 'caddc', 'co'),
                                           'clt', 'wbr'), 'wb')},
                            real_number(left), real_number(right), zero,
                            work.ap('ltsubadd', {'A': left, 'B': right,
                                                 'C': 'cc0'}))),
            work.ap('syl', {'ph': scope, 'ps': seq(right, 'cc', 'wcel'),
                            'ch': seq(seq('cc0', right, 'caddc', 'co'),
                                      right, 'wceq')},
                    work.ap('recnd', {'ph': scope, 'A': right},
                            real_number(right)),
                    work.ap('addlid', {'A': right})))

    def bound_reaches(self, work, total, added, left, right, real_number):
        """A term at most zero, said of the claim's two sides.

        The normalizer says the term is the claim's difference, and
        `suble0` says a difference at most zero is `<_` between them."""
        scope, span = work.under, seq(left, right, 'cmin', 'co')
        return work.ap(
            'mpbid', {'ph': scope, 'ps': seq(span, 'cc0', 'cle', 'wbr'),
                      'ch': seq(left, right, 'cle', 'wbr')},
            work.ap('eqbrtrd', {'ph': scope, 'A': span, 'B': total,
                                'C': 'cc0', 'R': 'cle'},
                    self.same_polynomial(work, span, total), added),
            work.ap('syl2anc',
                    {'ph': scope, 'ps': seq(left, 'cr', 'wcel'),
                     'ch': seq(right, 'cr', 'wcel'),
                     'th': seq(seq(span, 'cc0', 'cle', 'wbr'),
                               seq(left, right, 'cle', 'wbr'), 'wb')},
                    real_number(left), real_number(right),
                    work.ap('suble0', {'A': left, 'B': right})))

    def at_most_zero(self, work, said, fact, times, given, real_number):
        """One cited fact, scaled, as a term that is at most zero.

        Everything a sum takes is brought to that one shape first, so the
        addition has one case rather than one per relation. An equation is
        at most zero because it is zero exactly; an inequality already is,
        and scaling it by something positive leaves it so."""
        scope = work.under
        if said.variable is None and said.label == 'wn' \
                and len(said.children) == 1:
            said, given = self.unnegated(work, said.children[0], given,
                                         real_number)
        parts = order_sides(said)
        if parts is None:
            raise normal.Unhandled('a cited fact states no relation')
        was = [c.rpn(self.flabel) for c in said.children[:2]]
        gap = seq(was[0], was[1], 'cmin', 'co')
        real = work.ap('syl2anc',
                       {'ph': scope, 'ps': seq(was[0], 'cr', 'wcel'),
                        'ch': seq(was[1], 'cr', 'wcel'),
                        'th': seq(gap, 'cr', 'wcel')},
                       real_number(was[0]), real_number(was[1]),
                       work.ap('resubcl', {'A': was[0], 'B': was[1]}))
        numeral = field.spell_coefficient(times)
        if numeral is None:
            raise normal.Unhandled(f'{times} is past one digit')
        scaled = seq(numeral, gap, 'cmul', 'co')
        scaled_real = work.ap(
            'syl2anc', {'ph': scope, 'ps': seq(numeral, 'cr', 'wcel'),
                        'ch': seq(gap, 'cr', 'wcel'),
                        'th': seq(scaled, 'cr', 'wcel')},
            self.real_numeral(work, times), real,
            work.ap('remulcl', {'A': numeral, 'B': gap}))
        if parts[2] == '=':
            vanishes = work.chain(
                work.ap('oveq2d', {'ph': scope, 'A': gap, 'B': 'cc0',
                                   'C': numeral, 'F': 'cmul'},
                        self.difference_zero(work, was, given)),
                work.ap('syl', {'ph': scope,
                                'ps': seq(numeral, 'cc', 'wcel'),
                                'ch': seq(seq(numeral, 'cc0', 'cmul', 'co'),
                                          'cc0', 'wceq')},
                        work.coefficient(times),
                        work.ap('mul01', {'A': numeral})),
                scaled, seq(numeral, 'cc0', 'cmul', 'co'), 'cc0')
            return scaled, work.ap(
                'eqled', {'ph': scope, 'A': scaled, 'B': 'cc0'},
                scaled_real, vanishes), scaled_real
        if parts[2] == '<':
            # A sum that lands on `at most` has no use for the strictness,
            # so it is given up here and the one case below serves both.
            given = work.ap('ltled', {'ph': scope, 'A': was[0],
                                      'B': was[1]},
                            real_number(was[0]), real_number(was[1]), given)
        elif parts[2] != '<=':
            raise normal.Unhandled(f'a cited {parts[2]} is not written')
        bound = self.difference_le(work, was, given, None, real_number)
        if times == 1:
            return gap, bound, real
        if times <= 0:
            raise normal.Unhandled('a bound may only be scaled upward')
        return scaled, work.ap(
            'breqtrd', {'ph': scope, 'A': scaled,
                        'B': seq(numeral, 'cc0', 'cmul', 'co'), 'C': 'cc0',
                        'R': 'cle'},
            work.ap('mpbid',
                    {'ph': scope, 'ps': seq(gap, 'cc0', 'cle', 'wbr'),
                     'ch': seq(scaled, seq(numeral, 'cc0', 'cmul', 'co'),
                               'cle', 'wbr')},
                    bound,
                    work.ap('syl3anc',
                            {'ph': scope, 'ps': seq(gap, 'cr', 'wcel'),
                             'ch': seq('cc0', 'cr', 'wcel'),
                             'th': seq(seq(numeral, 'cr', 'wcel'),
                                       seq('cc0', numeral, 'clt', 'wbr'),
                                       'wa'),
                             'ta': seq(seq(gap, 'cc0', 'cle', 'wbr'),
                                       seq(scaled,
                                           seq(numeral, 'cc0', 'cmul', 'co'),
                                           'cle', 'wbr'), 'wb')},
                            real, work.a1i(seq('cc0', 'cr', 'wcel'), '0re'),
                            work.ap('jca',
                                    {'ph': scope,
                                     'ps': seq(numeral, 'cr', 'wcel'),
                                     'ch': seq('cc0', numeral, 'clt',
                                               'wbr')},
                                    self.real_numeral(work, times),
                                    work.a1i(seq('cc0', numeral, 'clt',
                                                 'wbr'),
                                             f'{times.numerator}pos')),
                            work.ap('lemul2', {'A': gap, 'B': 'cc0',
                                               'C': numeral}))),
            work.ap('syl', {'ph': scope, 'ps': seq(numeral, 'cc', 'wcel'),
                            'ch': seq(seq(numeral, 'cc0', 'cmul', 'co'),
                                      'cc0', 'wceq')},
                    work.coefficient(times),
                    work.ap('mul01', {'A': numeral}))), scaled_real

    def unnegated(self, work, inner, given, real_number):
        """A cited fact stated as a denial, said the other way round.

        `prime-above` reaches its bound by supposing the opposite and
        finding no witness, so what it has is `-. A < m` where the method
        wants `m <_ A`. `lenlt` is the one saying those are the same."""
        parts = order_sides(inner)
        if parts is None or parts[2] != '<':
            raise normal.Unhandled('only a denied `<` is turned round')
        was = [c.rpn(self.flabel) for c in inner.children[:2]]
        turned = self.to_term(seq(was[1], was[0], 'cle', 'wbr'))
        return turned, work.ap(
            'mpbird', {'ph': work.under,
                       'ps': seq(was[1], was[0], 'cle', 'wbr'),
                       'ch': seq(seq(was[0], was[1], 'clt', 'wbr'), 'wn')},
            given,
            work.ap('syl2anc',
                    {'ph': work.under, 'ps': seq(was[1], 'cr', 'wcel'),
                     'ch': seq(was[0], 'cr', 'wcel'),
                     'th': seq(seq(was[1], was[0], 'cle', 'wbr'),
                               seq(seq(was[0], was[1], 'clt', 'wbr'), 'wn'),
                               'wb')},
                    real_number(was[1]), real_number(was[0]),
                    work.ap('lenlt', {'A': was[1], 'B': was[0]})))

    def real_numeral(self, work, times):
        """( scope -> n e. RR ) for a whole multiplier."""
        whole = abs(times.numerator)
        held = work.a1i(seq(field.NUMERAL[whole], 'cr', 'wcel'),
                        f'{whole}re')
        if times.numerator >= 0:
            return held
        return work.ap('renegcld', {'ph': work.under,
                                    'A': field.NUMERAL[whole]}, held)

    def cited_fact(self, ref, said, scope, facts, lines):
        """The proof of one fact a cited line states.

        A line may say several things at once — `abs-bounds` concludes a
        pair of bounds — and what the step uses is one of them, so the
        line is taken apart the way `opposing` takes one apart."""
        want = said.rpn(self.flabel)
        held = self.carried(ref, facts, lines)
        if lines[ref].term == want:
            return held
        known = dict(facts)
        self.unpack(lines[ref].term, held, scope, known)
        if want not in known:
            raise normal.Unhandled('that line does not reach the fact')
        return known[want]

    def difference_le(self, work, was, given, facts, real_number):
        """( scope -> ( A - B ) <_ 0 ) from a cited A <_ B."""
        gap = seq(was[0], was[1], 'cmin', 'co')
        return work.ap(
            'mpbird', {'ph': work.under, 'ps': seq(gap, 'cc0', 'cle', 'wbr'),
                       'ch': seq(was[0], was[1], 'cle', 'wbr')},
            given,
            work.ap('syl2anc',
                    {'ph': work.under, 'ps': seq(was[0], 'cr', 'wcel'),
                     'ch': seq(was[1], 'cr', 'wcel'),
                     'th': seq(seq(gap, 'cc0', 'cle', 'wbr'),
                               seq(was[0], was[1], 'cle', 'wbr'), 'wb')},
                    real_number(was[0]), real_number(was[1]),
                    work.ap('suble0', {'A': was[0], 'B': was[1]})))

    def from_equation(self, cited, times, left, right, how, scope, facts,
                      lines):
        """The claim as one cited equation, scaled.

        An equation may be multiplied by anything, which is what lets one
        cited equation carry a claim on its own. A combination that uses
        an inequality needs that inequality scaled and added, and is a
        different proof."""
        ref, said = cited
        parts = order_sides(said)
        if parts is None or parts[2] != '=':
            raise normal.Unhandled('the cited fact is not an equation')
        numeral = field.spell_coefficient(times)
        if numeral is None:
            raise normal.Unhandled(f'{times} is past one digit')

        def complex_number(term):
            want = seq(term, 'cc', 'wcel')
            if want in facts:
                return facts[want]
            return self.settle(self.to_term(want), scope, facts)

        work = normal.Emitter(self.sigs, scope, complex_number)
        was = [c.rpn(self.flabel) for c in said.children]
        gap = seq(was[0], was[1], 'cmin', 'co')
        scaled = seq(numeral, gap, 'cmul', 'co')
        span = seq(left, right, 'cmin', 'co')
        def real_number(one):
            want = seq(one, 'cr', 'wcel')
            if want in facts:
                return facts[want]
            return self.settle(self.to_term(want), scope, facts)

        if parts[2] == '=':
            # The cited equation says its difference is zero; scaled, that
            # is the claim's difference, and the normalizer is what says so.
            reached = work.chain(
                self.same_polynomial(work, span, scaled),
                work.chain(
                    work.ap('oveq2d', {'ph': scope, 'A': gap, 'B': 'cc0',
                                       'C': numeral, 'F': 'cmul'},
                            self.difference_zero(
                                work, was,
                                self.cited_fact(ref, said, scope, facts,
                                                lines))),
                    work.ap('syl',
                            {'ph': scope, 'ps': seq(numeral, 'cc', 'wcel'),
                             'ch': seq(seq(numeral, 'cc0', 'cmul', 'co'),
                                       'cc0', 'wceq')},
                            work.coefficient(times),
                            work.ap('mul01', {'A': numeral})),
                    scaled, seq(numeral, 'cc0', 'cmul', 'co'), 'cc0'),
                span, scaled, 'cc0')
            if how == '=':
                return work.ap(
                    'mpbid', {'ph': scope, 'ps': seq(span, 'cc0', 'wceq'),
                              'ch': seq(left, right, 'wceq')},
                    reached,
                    work.ap('syl2anc',
                            {'ph': scope, 'ps': seq(left, 'cc', 'wcel'),
                             'ch': seq(right, 'cc', 'wcel'),
                             'th': seq(seq(span, 'cc0', 'wceq'),
                                       seq(left, right, 'wceq'), 'wb')},
                            complex_number(left), complex_number(right),
                            work.ap('subeq0', {'A': left, 'B': right})))
            if how != '<=':
                raise normal.Unhandled(f'a {how} conclusion is not written')
            # A difference that is zero is at most zero.
            at_most = work.ap(
                'eqled', {'ph': scope, 'A': span, 'B': 'cc0'},
                work.ap('syl2anc',
                        {'ph': scope, 'ps': seq(left, 'cr', 'wcel'),
                         'ch': seq(right, 'cr', 'wcel'),
                         'th': seq(span, 'cr', 'wcel')},
                        real_number(left), real_number(right),
                        work.ap('resubcl', {'A': left, 'B': right})),
                reached)
        else:
            raise normal.Unhandled(f'a {how} conclusion is not written')
        # A difference at most zero is what `<_` says of the two sides.
        return work.ap(
            'mpbid', {'ph': scope, 'ps': seq(span, 'cc0', 'cle', 'wbr'),
                      'ch': seq(left, right, 'cle', 'wbr')},
            at_most,
            work.ap('syl2anc',
                    {'ph': scope, 'ps': seq(left, 'cr', 'wcel'),
                     'ch': seq(right, 'cr', 'wcel'),
                     'th': seq(seq(span, 'cc0', 'cle', 'wbr'),
                               seq(left, right, 'cle', 'wbr'), 'wb')},
                    real_number(left), real_number(right),
                    work.ap('suble0', {'A': left, 'B': right})))

    def difference_zero(self, work, was, given):
        """( scope -> ( A - B ) = 0 ) from a cited A = B."""
        scope = work.under
        return work.ap(
            'mpbird', {'ph': scope, 'ps': seq(seq(was[0], was[1], 'cmin',
                                                  'co'), 'cc0', 'wceq'),
                       'ch': seq(was[0], was[1], 'wceq')},
            given,
            work.ap('syl2anc',
                    {'ph': scope, 'ps': seq(was[0], 'cc', 'wcel'),
                     'ch': seq(was[1], 'cc', 'wcel'),
                     'th': seq(seq(seq(was[0], was[1], 'cmin', 'co'), 'cc0',
                                   'wceq'), seq(was[0], was[1], 'wceq'),
                               'wb')},
                    work.atom(was[0]), work.atom(was[1]),
                    work.ap('subeq0', {'A': was[0], 'B': was[1]})))

    def decide_order(self, step, term, lines):
        """Refuse an `inequalities` step that does not follow from its lines.

        A cited line of several sentences supplies each sentence that is a
        linear fact and is ignored for the rest, so citing a line that also
        states a membership is not an error."""
        claim = linear.fact(self.to_term(term), self.flabel)
        if claim is None:
            return                               # not a relation this decides
        given = []
        for ref in step.just.refs:
            held = lines.get(ref)
            if held is None:
                continue
            for said in self.parts(held.term):
                one = linear.fact(self.to_term(said), self.flabel)
                if one is not None:
                    given.append(one)
        if not linear.follows(given, claim):
            raise Problem('', step.line,
                          f'{self.render(term)} does not follow from what '
                          f'step {fmt(step.number)} cites')

    def equivalent(self, step, node, term, scope, facts, lines):
        """A definition whose right side is not an existence claim.

        `def:irrational` says x is irrational exactly when x is real and not
        rational, and the step cites the two lines that say each. The lemma
        gives the biconditional and the lines give its right side, so the
        definition is read the way the text reads it: right to left."""
        item = self.items[step.just.head.split(':', 1)[1]]
        return self.trying(item, step, self.one_equivalent, term, scope,
                           facts, lines)

    def one_equivalent(self, lemma, step, term, scope, facts, lines):
        # What a lemma's right side says beyond what its left fixes can
        # only come from the lines the step cites, offered in the order the
        # step writes them.
        said = [lines[ref].term for ref in step.just.refs if ref in lines]
        hint = said[0] if said else None
        for extra in said[1:]:
            hint = seq(hint, extra, 'wa')
        # No name is introduced here: the claim already carries whatever the
        # lemma binds, and the match is what says which variable that is.
        says, right = self.unfolding(step, lemma, term, None, None, None,
                                     scope, facts, hint=hint)
        return seq(scope, term, right,
                   self.settle(self.to_term(right), scope, facts,
                               step=step, lines=lines), says,
                   'mpbird')

    def turned(self, rpn):
        """The same two-sided claim with its sides the other way round."""
        node = self.to_term(rpn)
        if len(node.children) != 2:
            return None
        return seq(node.children[1].rpn(self.flabel),
                   node.children[0].rpn(self.flabel), node.label)

    def unfolded(self, step, node, term, scope, facts, lines):
        """A definition unfolded to reach one part of what it says.

        `def:set-builder` says that belonging to {t ∈ X : P(t)} is belonging
        to X and having the property, and Cantor's step 3.1.3.1 wants the
        second of those from a line that says the first. So the definition
        is read left to right and what it gives is taken apart."""
        item = self.items[step.just.head.split(':', 1)[1]]
        return self.trying(item, step, self.one_unfolded, term, scope, facts,
                           lines)

    def one_unfolded(self, lemma, step, term, scope, facts, lines):
        sig = self.sigs[lemma]
        whole = self.syntax.statement(sig)
        variables, reads = whole.names(), whole
        while reads.label == 'wi':
            reads = reads.children[1]
        if reads.label != 'wb':
            raise Problem('', step.line, f'{lemma} states no biconditional')
        # A line may say several things at once, and what the definition
        # unfolds is any one of them: the primes proof obtains a natural
        # number, its primality and what it divides on a single line, and it
        # is the middle conjunct that `isprm2` unfolds.
        for ref in step.just.refs:
            cited = lines.get(ref)
            if cited is None:
                continue
            held = {cited.term: self.carried(ref, facts, lines)}
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
            raise Problem('', step.line,
                          f'no cited line is what {lemma} unfolds')
        # What the left side fixes need not be everything the right side
        # holds: `rabid` learns the property from the claim itself.
        for spelt in self.parts(reads.children[1].rpn(self.flabel)):
            filled = kernel.match(self.to_term(spelt), self.to_term(term),
                                  dict(binding), variables)
            if filled is not None:
                binding = filled
                break

        left = reads.children[0].substitute(binding).rpn(self.flabel)
        right = reads.children[1].substitute(binding).rpn(self.flabel)
        says, _given = self.unfolding(step, lemma, left, right, None, None,
                                      scope, facts)
        proof = seq(scope, left, right, given, says, 'mpbid')
        known = {right: proof}
        self.unpack(right, proof, scope, known)
        if term in known:
            return known[term]
        # What the unfolding says and how the readable line spells it are
        # allowed to differ, so long as set.mm says they are the same claim:
        # `isprm2` writes p > 1 as membership of ZZ>=2, and `eluz2gt1` is
        # the declared lemma that carries one to the other.
        try:
            return self.settle(self.to_term(term), scope,
                               {**facts, **known}, step=step, lines=lines)
        except Problem:
            raise Problem('', step.line,
                          f'{lemma} does not say {self.render(term)}') from None

    def trying(self, item, step, way, term, scope, facts, lines):
        """Use whichever lemma the target names reaches the claim.

        A definition may be supplied by more than one, differing in what
        they ask: `rabid` says what belongs to a set-builder when the
        element is the name the builder binds, and `elrab` when it is
        anything else, and only one of the two can be right of any step."""
        trouble = None
        for lemma in targets.clauses(item):
            try:
                return way(lemma, step, term, scope, facts, lines)
            except Problem as said:
                trouble = said
        raise trouble

    def reading(self, item, term):
        """Which of three ways a biconditional definition reaches a claim.

        The claim decides, and what the lemma states decides with it. A
        definition reaching an existence claim supplies a witness; one whose
        right side the step already holds is read right to left; one whose
        left side the step holds is unfolded and taken apart.

        Every lemma the target names is asked, not just the first: `rabid`
        and `elrab` say the same thing of a set-builder and differ only in
        what they ask, so which of the two fits says nothing about which
        way the definition is being read."""
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
        elaborates to the conjunction of the six equations `def:congruent`
        lists, so a step reading one of them off names the definition but
        asks for nothing the file does not have: the claim is a conjunct,
        and `unpack` reaches it."""
        found = self.projected(step, term, scope, facts, lines)
        if found is not None:
            return found
        return self.assume(step, term, scope, facts, 'def', lines)

    def projected(self, step, term, scope, facts, lines):
        """The claim, when a line the step cites is a conjunction stating it.

        The depth is the six conjuncts of a congruence, which nest to the
        left, so reaching the first of them costs five."""
        for ref in step.just.refs:
            cited = lines[ref]
            known = dict(facts)
            self.unpack(cited.term, self.carried(ref, facts, lines),
                        scope, known, depth=8)
            if term in known:
                return known[term]
        return None

    def unfold_equation(self, step, node, term, scope, facts, lines):
        """A definition stated as an equation, one clause per `then` group.

        `def:S` says what S(1) is and what S(n + 1) is, and set.mm proves each
        separately. The clause is chosen by which lemma's conclusion is what
        the step claims, so the text never says which."""
        item = self.items[step.just.head.split(':', 1)[1]]
        goal = self.to_term(term)
        for label in targets.split_entries(item.fields['target']):
            found = self.apply_lemma(label, goal, scope, facts, step)
            if found is not None:
                return found
        raise Problem('', step.line,
                      f'no clause of {step.just.head} gives what step '
                      f'{fmt(step.number)} claims')

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

        The bridge comes from `targets.MEMBERSHIP` and nowhere else, which
        is the rule that stops an elaborator reaching a claim by whatever it
        can find that fits."""
        variables = whole.names()
        want = goal.rpn(self.flabel)
        for bridge in targets.MEMBERSHIP:
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
                if found is None:
                    continue
                try:
                    alike = self.settle(self.to_term(seq(said, want, 'wb')),
                                        scope, facts)
                except Problem:
                    continue
                return seq(scope, said, want, found, alike, 'mpbid')
        return None

    def apply_lemma(self, label, goal, scope, facts, step, crossing=True):
        """Apply one set.mm lemma to reach a claim, side conditions and all.

        What a lemma states before the claim it reaches may be an
        implication or a biconditional: `dvds1` says that on ℕ0, dividing
        one and being one are the same, and a step citing it has the
        dividing and wants the being. Both are peeled, and which one each
        was decides how it is discharged."""
        sig = self.sigs[label]
        whole = self.syntax.statement(sig)
        variables = whole.names()
        antecedents, joins, reads, binding = [], [], whole, None
        while True:
            binding = kernel.match(reads, goal, {}, variables)
            if binding is not None:
                break
            if reads.label not in ('wi', 'wb'):
                return (self.crossed(label, whole, reads, goal, scope,
                                     facts, step) if crossing else None)
            # A biconditional says one thing and reaching it either way is
            # reaching it: `elnnz` says a natural number is an integer above
            # zero, and a step with the integer and the bound wants the
            # natural number, which is the side a forward read peels off.
            # Tried only where the forward read has already failed, so a
            # lemma that fits as it stands fits as it always did.
            if reads.label == 'wb':
                turned = kernel.match(reads.children[0], goal, {}, variables)
                if turned is not None:
                    antecedents.append(reads.children[1])
                    joins.append(TURNED)
                    binding, reads = turned, reads.children[0]
                    break
            antecedents.append(reads.children[0])
            joins.append(reads.label)
            reads = reads.children[1]

        # The scope is where a lemma's disjointness conditions can forbid it,
        # so it is chosen before anything is built. ELABORATION.md 14.
        where, frame = self.allowed(sig, binding, variables)
        known = self.supplied(step, where, self.frames_facts(frame, facts))
        for slot in antecedents:
            if not slot.names() - set(binding):
                continue
            if slot.variable is not None:
                binding[slot.variable] = self.to_term(where)
                continue
            # What the lemma concludes need not fix everything it asks, so
            # an antecedent that is still open is matched against something
            # the step already has: `orel2` learns which disjunct is ruled
            # out from the line that rules it out.
            for held in known:
                filled = kernel.match(slot, self.to_term(held), dict(binding),
                                      variables)
                if filled is not None:
                    binding = filled
                    break
        essentials = [self.prove_essential(
            self.syntax.parse(e[1:], 'wff').substitute(binding), where, known)
            for e in sig.essentials]
        proof = self.ap(label, self.spelt(binding), *essentials)
        if not antecedents:
            # The lemma asks nothing, so it states the claim outright and has
            # to be brought into the scope the step sits in.
            return self.carry(seq(goal.rpn(self.flabel), where, proof, 'a1i'),
                              goal.rpn(self.flabel), frame)
        for i, slot in enumerate(antecedents):
            asks = slot.substitute(binding)
            if asks.rpn(self.flabel) == where:
                continue                      # the deduction slot
            rest = goal.rpn(self.flabel)
            for later, join in reversed(list(zip(antecedents[i + 1:],
                                                 joins[i + 1:], strict=True))):
                if later.substitute(binding).rpn(self.flabel) != where:
                    if join is TURNED:
                        raise Problem('', step.line if step else 0,
                                      f'{label} asks something past a '
                                      f'biconditional it states the other '
                                      f'way round')
                    rest = seq(later.substitute(binding).rpn(self.flabel),
                               rest, join)
            first = proof.split()[-1] == label
            fold = {('wi', True): 'syl', ('wi', False): 'mpd',
                    ('wb', True): 'sylib', ('wb', False): 'mpbid',
                    (TURNED, True): 'sylibr', (TURNED, False): 'mpbird'}
            proof = seq(where, asks.rpn(self.flabel), rest,
                        self.settle(asks, where, known), proof,
                        fold[(joins[i], first)])
        return self.carry(proof, goal.rpn(self.flabel), frame)

    def prove_essential(self, want, scope, facts):
        """One hypothesis a lemma states in full rather than asking for."""
        if want.label != 'wi':
            return self.settle(want, scope, facts)
        left, right = want.children
        under = left.rpn(self.flabel)
        if under == right.rpn(self.flabel):
            return seq(under, 'id')
        # A lemma may state its instance rather than ask for it: `elrab`
        # says what belongs to a set-builder by way of the body read at the
        # element, and wants the body before and after tied together.
        if (left.label == 'wceq' and right.label == 'wb'
                and left.children[0].label == 'cv'):
            was = left.children[0].rpn(self.flabel)
            now = left.children[1].rpn(self.flabel)

            def stands(one, other, _where, _held):
                return (seq(under, 'id')
                        if one.rpn(self.flabel) == was
                        and other.rpn(self.flabel) == now else None)
            return self.congruence(right.children[0], right.children[1],
                                   under, {}, None, stands)
        if under == scope:
            return self.settle(right, scope, facts)
        if (left.label == 'wa'
                and left.children[0].rpn(self.flabel) == scope):
            extra = left.children[1].rpn(self.flabel)
            wider = {k: seq(under, scope, k, seq(scope, extra, 'simpl'), v,
                            'syl') for k, v in facts.items()}
            wider[extra] = seq(scope, extra, 'simpr')
            return self.settle(right, under, wider)
        return self.settle(right, under, {})

    def allowed(self, sig, binding, variables):
        """The innermost scope a lemma's disjointness conditions permit.

        `fsump1` forbids its summation variable in the antecedent, and the
        induction hypothesis is an equation between sums, so it holds that
        variable. The step is written inside that scope and cannot be proved
        there. It is proved one frame out and carried back in."""
        forbidden = set()
        for a, b in sig.disjoint:
            for one, other in ((a, b), (b, a)):
                if one in binding and other not in binding:
                    forbidden |= {self.flabel.get(n, n)
                                  for n in binding[one].names()}
        for index in range(len(self.frames) - 1, -1, -1):
            term = self.frames[index][0]
            if not forbidden & set(term.split()):
                return term, index
        raise Problem('', 0, 'no scope satisfies the lemma')

    def frames_facts(self, frame, facts):
        """What is known at one frame, which is what was known when it opened."""
        return facts if frame == len(self.frames) - 1 else self.frames[frame][2]

    def carry(self, proof, claim, frame):
        """Bring a proof from an outer frame back to the innermost one."""
        for index in range(frame, len(self.frames) - 1):
            outer, added = self.frames[index][0], self.frames[index + 1][1]
            proof = seq(outer, claim, added, proof, 'adantr')
        return proof

    def assume(self, step, term, scope, facts, prefix, lines):
        """State what a step claims, under everything it rests on, and take
        it. What the file assumes is listed at its head.

        Everything it rests on is the lines it cites as well as the
        conditions it writes. A step reading `inequalities, from 3, 4` that
        assumed only its `requires` lines would assume that the sum of two
        numbers is at most the sum of their absolute values, which is the
        theorem; under the lines it cites it assumes only that two
        inequalities may be added, which is what the method is for. The
        cited lines are also why the file needs the proofs above it: an
        assumption that drops them leaves them unused and unchecked."""
        asks = []
        for ref in step.just.refs:
            cited = lines[ref]
            asks.append((cited.term, self.carried(ref, facts, lines)))
        for want, (_t, how, _l) in zip(
                [self.read(t) for t, _h, _l in step.requires], step.requires,
                strict=True):
            here = self.term(want)
            if here not in [a for a, _p in asks]:
                asks.append((here, self.side(want, how, scope, facts)))

        statement = term
        for one, _given in reversed(asks):
            statement = seq(one, statement, 'wi')
        proof = self.stated(prefix, '|- ' + self.render(statement))
        if not asks:
            # Nothing to discharge, so the statement is simply taken at the
            # scope the step sits in.
            return seq(term, scope, proof, 'a1i')
        # The conditions nest, outermost first, so each is answered in turn
        # and what is left of the statement shrinks by one.
        for i, (one, given) in enumerate(asks):
            rest = term
            for later, _p in reversed(asks[i + 1:]):
                rest = seq(later, rest, 'wi')
            proof = seq(scope, one, rest, given, proof,
                        'syl' if i == 0 else 'mpd')
        return proof

    def stated(self, prefix, text):
        """Register a statement this file takes rather than proves.

        What a statement asks to be pushed is every variable it mentions, in
        the order the database declares them, which is not the order the
        statement happens to write them in. The same statement asked for
        twice is listed once: two steps may need the same arithmetic."""
        if text in self.assumed:
            return self.assumed[text]
        label = self.fresh(prefix)
        self.axioms.append((label, text))
        free = sorted({t for t in text.split() if t in self.flabel},
                      key=lambda v: self.forder[self.flabel[v]])
        self.sigs[label] = Signature(
            label, '$a', text.split(),
            [(self.sigs[self.flabel[v]].statement[0], v) for v in free])
        self.assumed[text] = seq(*(self.flabel[v] for v in free), label)
        return self.assumed[text]

    def binder_var(self, name):
        """The setvar a binder's name stands for.

        A name is a letter and set.mm may have declared that letter as a
        class: Cantor quantifies over B, and B there is a class variable.
        So the letter's own label is taken only when it names a setvar, and
        a spare stands in otherwise — the same one every time, since the
        name is one name wherever the proof writes it."""
        if name in self.bound_as:
            return self.bound_as[name]
        label = self.flabel.get(name)
        if not (label and self.sigs[label].statement[0] == 'setvar'):
            label = self.spare_var()
        self.bound_as[name] = label
        return label

    def fixed_var(self, name):
        """The variable a fixed name takes.

        Its own letter where nothing else is holding it, because the claim
        the block states binds that letter and the two have to agree: the
        `fix` in Cantor introduces the x that `for every x ∈ A` quantifies.
        A spare otherwise, as when a notation already binds the letter."""
        own = self.flabel.get(name)
        held = {t.split()[0] for t in self.names.values()
                if isinstance(t, str) and t.endswith(' cv')}
        if own and own not in held and own not in self.taken:
            return own
        return self.spare_var()

    def spare_var(self):
        """A kernel variable no name in this proof is already standing for.

        The names a proof introduces do not all come from here: the first
        `obtain` takes its variables from the existential the item states, so
        a later step asking for a spare can be handed one of them."""
        held = {t.split()[0] for t in self.names.values()
                if isinstance(t, str) and t.endswith(' cv')} | self.reserved
        while self.spare and self.spare[0] in held:
            self.spare.pop(0)
        if not self.spare:
            raise Problem('', 0, 'no variable left to introduce a name with')
        return self.spare.pop(0)

    def fresh(self, prefix):
        """A label for a generated statement nothing else is using.

        `ine1` reads as the first inequality assumed; set.mm reads it as
        `_i =/= 1`, and a file that includes another numbers its own from one
        as well. So the label says which file it belongs to, and is looked
        for rather than taken: the library is large enough that a short name
        is never safely free."""
        stem = label_of(self.thm.name, self.sigs)
        number = len(self.axioms) + 1
        while f'{stem}.{prefix}{number}' in self.sigs:
            number += 1
        return f'{stem}.{prefix}{number}'

    def supplied(self, step, scope, facts):
        """The facts a step's own `requires` lines put within reach.

        A lemma asks for what it asks for, and the text writes what a reader
        would want written: `resqrtth` wants 0 ≤ 2 and the step says so. The
        lines are proved once and offered alongside what the scope holds."""
        known = dict(facts)
        for text, how, _line in step.requires:
            want = self.read(text)
            term = self.term(want)
            if term not in known:
                known[term] = self.side(want, how, scope, known)
        return known

    def side(self, want, how, scope, facts):
        """A proof of what one `requires` line asks for.

        A `requires` line may name the lines it rests on, and a method that
        is not expanded has to say so. `requires q ≠ 0: inequalities, from
        3.1` asks only that a positive number is not zero; an assumption
        that drops the 3.1 asks that the number is not zero, which is more
        than the line says and leaves 3.1 unused."""
        term = self.term(want)
        if term in facts:
            return facts[term]
        closure = how.strip().split(',')[0].strip()
        # A line naming a method is discharged by the method it names. A
        # closed numeral inequality is what `arithmetic` decides outright,
        # and a declared lemma reaching the same fact reaches it the long
        # way round: 1 < 2 through membership of ℤ≥2 costs five lemmas.
        if closure == 'arithmetic':
            try:
                return self.prove_numeral(term, scope, facts)
            except (normal.Unhandled, Problem):
                pass
        try:
            return self.settle(self.to_term(term), scope, facts)
        except Problem:
            pass
        if want.notation == 'membership':
            return self.closure(want.children[0],
                                self.term(want.children[1]), scope, facts)
        if closure == 'arithmetic':
            # A value is the other thing `arithmetic` decides, and a closed
            # one is an identity of the field with no atoms in it, so it
            # goes where identities go rather than wanting a second
            # procedure. `METHODS.md` lists the two as one method.
            try:
                return self.prove_field(None, term, scope, facts, self.lines)
            except (normal.Unhandled, Problem):
                pass
        if closure == 'inequalities':
            # A side condition resting on a method is proved the way a step
            # resting on it is, where the method can prove one at all.
            try:
                return self.prove_order(citations(how), term, scope, facts,
                                        self.lines)
            except (normal.Unhandled, Problem):
                pass
        if closure in ('arithmetic', 'inequalities', 'algebra'):
            # A side condition resting on a closure method rests on it the
            # same way a step does, and is listed the same way: under what
            # the line cites, and under nothing else.
            asks = [(self.lines[ref].term,
                     self.carried(ref, facts, self.lines))
                    for ref in citations(how) if ref in self.lines]
            statement = term
            for one, _given in reversed(asks):
                statement = seq(one, statement, 'wi')
            proof = self.stated(closure[:3], '|- ' + self.render(statement))
            if not asks:
                return seq(term, scope, proof, 'a1i')
            for i, (one, given) in enumerate(asks):
                rest = term
                for later, _p in reversed(asks[i + 1:]):
                    rest = seq(later, rest, 'wi')
                proof = seq(scope, one, rest, given, proof,
                            'syl' if i == 0 else 'mpd')
            return proof
        raise Problem('', 0, f'cannot supply {self.render(term)}')

    def calculation(self, step, node, term, scope, facts, lines):
        """A chain folded by transitivity, one link at a time.

        A link carries a relation of its own, and they need not all be the
        same: the triangle inequality runs two equalities into a `≤`. So each
        link is read as the claim relating the run so far to what the link
        adds, and the lemma that folds it is chosen by the two relations
        either side of the join.

        A link may cite a line the other way round — `3.3, right to left` —
        because nothing in the readable layer says which way an equation
        faces, and the chain wants them all facing the same way."""
        links = []
        for text, _line in step.just.chain:
            turned = 'right to left' in text
            body = re.sub(r',\s*right to left\s*$', '', text).strip()
            body, cite = body.rsplit(None, 1)
            links.append((body.strip(), cite, turned))

        def held(cite, turned):
            line = lines[cite]
            proof = self.carried(cite, facts, lines)
            if not turned:
                return proof
            was, now = (c.rpn(self.flabel)
                        for c in self.to_term(line.term).children)
            return seq(scope, was, now, proof, 'eqcomd')

        first = self.read(links[0][0])
        if not first.text:
            raise Problem('', step.line, 'a chain starts with no relation')
        words = links[0][0].split()
        rest = ' '.join(words[words.index(first.text) + 1:])
        whole = self.to_term(self.term(first))
        left = whole.children[0].rpn(self.flabel)
        right = whole.children[1].rpn(self.flabel)
        said = whole.label
        relation = whole.children[2].rpn(self.flabel) if said == 'wbr' else ''
        proof = held(links[0][1], links[0][2])
        for body, cite, turned in links[1:]:
            mark, added = body.split(None, 1)
            joined = self.to_term(self.term(self.read(f'{rest} {mark} {added}')))
            fold = self.FOLDING.get((said, joined.label))
            if fold is None:
                raise Problem('', step.line,
                              f'no transitivity folds {said} into '
                              f'{joined.label}')
            if joined.children[0].rpn(self.flabel) != right:
                raise Problem('', step.line,
                              'a link that reads the other way round from the '
                              'one above it')
            nxt = joined.children[1].rpn(self.flabel)
            if joined.label == 'wbr':
                relation = joined.children[2].rpn(self.flabel)
            proof = seq(scope, left, right, nxt, relation, proof,
                        held(cite, turned), fold)
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
        coming from a different place. `ELABORATION.md` requirement 7."""
        whole = self.to_term(term)
        if whole.label != 'wrex':
            raise Problem('', step.line, 'an exhibit that claims no existence')
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
            raise Problem('', step.line, 'no cited line names a witness')

        saved = dict(self.names)
        self.names[said] = stands
        shape = self.freeze(node.children[2])
        self.names = saved
        at = seq(stands, witness, 'wceq')
        here, instance = self.rewrite(shape, stands, witness, at,
                                      seq(at, 'id'))

        known = self.supplied(step, scope, facts)
        member = seq(witness, domain.rpn(self.flabel), 'wcel')
        return seq(scope, seq(member, here, 'wa'), term,
                   seq(scope, member, here,
                       self.settle(self.to_term(member), scope, known),
                       self.settle(self.to_term(here), scope, known), 'jca'),
                   body.rpn(self.flabel), here, self.binder_var(said),
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
        a place that has to agree does not."""
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

    def aligned(self, pattern, actual, marks, found):
        """Whether these agree everywhere but the marked places."""
        here = pattern.rpn(self.flabel)
        if here in marks:
            was = actual.rpn(self.flabel)
            return found.setdefault(here, was) == was
        if pattern.variable is not None or actual.variable is not None:
            return pattern.variable == actual.variable
        if pattern.label != actual.label:
            return False
        if len(pattern.children) != len(actual.children):
            return False
        return all(self.aligned(a, b, marks, found)
                   for a, b in zip(pattern.children, actual.children,
                                   strict=True))

    def conclude(self, step, node, term, scope, facts, lines):
        """A definition used the other way: to conclude an existence claim.

        The witness is never written in the text. It is read off the cited
        line, by walking the shape the definition states against it."""
        subject = self.term(self.read(instantiation(step.just.text)[0][1]))
        var = self.spare_var()
        saved = dict(self.names)
        # A definition may name more than the thing it is about: `def:divides`
        # is about d and says what it divides, and the step fills in both.
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
        for ref in step.just.refs:
            cited = lines[ref]
            held = self.to_term(cited.term)
            witness = None
            for shape in (body, self.turned(body)):
                if shape is not None:
                    witness = self.witness_in(self.to_term(shape), held, mark)
                if witness:
                    break
            if witness is None:
                continue
            here = self.term(self.substituted(kernel, mark, witness))
            if cited.term in (here, self.turned(here)):
                break
        else:
            raise Problem('', step.line, 'no cited line names a witness')
        at = seq(f'{var} cv', witness, 'wceq')
        _built, instance = self.rewrite(kernel, f'{var} cv', witness, at,
                                        seq(at, 'id'))

        ex = seq(body, var, over, 'wrex')
        member = seq(witness, over, 'wcel')
        p_member = self.required(step, member, over, scope, facts)
        # The cited line faces the way the text writes the definition, and
        # the existential faces the way the lemma writes it.
        # A line proved before a block opened holds inside it too, and the
        # scope's own copy is what says so where the step sits.
        p_cited = facts.get(cited.term, cited.proof)
        if cited.term != here:
            was = self.to_term(cited.term)
            p_cited = seq(scope, *(c.rpn(self.flabel) for c in was.children),
                          p_cited, 'eqcomd')
        p_ex = seq(scope, seq(member, here, 'wa'), ex,
                   seq(scope, member, here, p_member, p_cited, 'jca'),
                   body, here, var, witness, over, instance, 'rspcev', 'syl')

        return seq(scope, term, ex, p_ex,
                   self.unfolding(step, lemma, term, ex, var, over, scope,
                                  facts)[0],
                   'mpbird')

    def join(self, step, node, term, scope, facts, lines):
        """Two lines paired, which is one thing inside a contradiction and
        another outside it.

        Inside, it emits nothing: `pm2.65d` closes the block and consumes
        both joined lines itself, so the join only records which pair. Inside
        a case it is `jca`, and the lines are paired by what they claim, since
        the text lists them in the order they were derived and the conclusion
        states them in the theorem's order. `ELABORATION.md` requirement 8."""
        self.joined = [lines[ref].term for ref in step.just.refs]
        if self.enclosing is not None \
                and self.enclosing.owner.just.head == 'contradiction':
            return None
        wanted = self.claim_of(' '.join(step.claim))
        held = {lines[ref].term: self.carried(ref, facts, lines)
                for ref in step.just.refs}
        left, right = self.to_term(wanted).children
        pair = [left.rpn(self.flabel), right.rpn(self.flabel)]
        if not all(p in held for p in pair):
            raise Problem('', step.line,
                          'the joined lines are not what the step claims')
        return seq(scope, *pair, *(held[p] for p in pair), 'jca')

    def cite(self, step, node, term, scope, facts, lines):
        """A theorem cited. Either set.mm supplies it or this corpus does."""
        item = self.items[step.just.head.split(':', 1)[1]]
        if 'proved-in' in item.fields:
            return self.cite_corpus(step, term, scope, facts, lines, item)
        return self.cite_library(step, term, scope, facts, lines, item)

    def cite_library(self, step, term, scope, facts, lines, item):
        """Apply the set.mm theorem the item's `target` names.

        The lemma is stated in its own variables and the item in the readable
        ones, and reading the lemma's statement is what relates them: its
        conclusion is matched against what the step claims, and what that
        leaves open is fixed by matching an antecedent against a line the
        step already has."""
        labels = targets.clauses(item)
        if not labels:
            # Nothing in the library has its shape, so the file states what
            # it claims and lists it, the same as an item obtained from.
            # `thm:lowest-terms` is the case, and `thm:angle-symmetric`.
            return self.assume_item(step, term, scope, facts, item)
        for label in labels:
            found = self.apply_lemma(label, self.to_term(term), scope, facts,
                                     step)
            if found is not None:
                return found
        raise Problem('', step.line,
                      f'no clause of {step.just.head} reaches what step '
                      f'{fmt(step.number)} claims')

    def cite_corpus(self, step, term, scope, facts, lines, item):
        """Apply a theorem this corpus proves, as this elaborator states it.

        Its hypotheses became the antecedent of one implication, so citing it
        is conjoining the facts the step supplies and applying one label."""
        other = self.proofs[item.name]
        if item.name not in self.cited:
            self.cited.append(item.name)
        saved, kept = dict(self.names), dict(self.sets)
        spare = list(CLASS_NAMES)
        written = dict(instantiation(step.just.text))
        for kind, htext, _label, _line in other.hypotheses:
            node = self.read(hypothesis_body(kind, htext))
            if kind == 'let' and node.notation == 'membership':
                name = node.children[0].text
                self.names[name] = (self.term(self.read(written[name]))
                                    if name in written else spare.pop(0))
        wanted = [self.term(self.read(hypothesis_body(kind, htext)))
                  for kind, htext, _l, _n in other.hypotheses]
        self.names, self.sets = saved, kept

        pair = wanted[0]
        proof = facts[wanted[0]]
        for extra in wanted[1:]:
            proof = seq(scope, pair, extra, proof, facts[extra], 'jca')
            pair = seq(pair, extra, 'wa')
        pushed = [self.term(self.read(v)) for _n, v in
                  instantiation(step.just.text)]
        return seq(scope, pair, term, proof, *pushed,
                   label_of(item.name, self.sigs), 'syl')

    def required(self, step, goal, want, scope, facts):
        """The `requires` line that supplies one side condition.

        A lemma can ask for more than the text writes: `divides` wants both
        sides of `d || n` in ZZ, and only the side a reader could doubt is
        written down. What no line supplies is settled from the term."""
        if goal in facts:
            return facts[goal]
        for text, _how, _line in step.requires:
            node = self.read(text)
            if self.term(node) == goal:
                return self.closure(node.children[0], want, scope, facts)
        try:
            return self.settle(self.to_term(goal), scope, facts)
        except Problem:
            raise Problem('', step.line,
                          f'no requires line for {self.render(goal)}') from None

    def freeze(self, node):
        """The tree with its leaves turned into the terms they stand for.

        A definition's body is read with the definition's own names bound,
        and those names may be the ones the proof is using for something
        else: `def:odd` binds `k` and so does the step that obtains from it.
        Freezing the tree settles what it means before the names change
        back. A binder's own variable is left alone: it stands for itself,
        and the slot it fills wants the variable rather than a term saying
        what the variable means."""
        if not node.children:
            return _Literal(self.term(node))
        # The body speaks of what the binder introduces, so the name stands
        # for its own variable while the body is frozen, exactly as `term`
        # does it. Without this the body's leaves are read against whatever
        # the proof happens to be holding, which is nothing once the block
        # that fixed a name of the same spelling has closed.
        bound = self.binders.get(node.notation, ())
        saved = dict(self.names)
        for i in bound:
            said = node.children[i].text
            self.names[said] = f'{self.binder_var(said)} cv'
        frozen = Node(node.notation, node.sort,
                      [c if i in bound else self.freeze(c)
                       for i, c in enumerate(node.children)], node.text)
        if bound:
            self.names = saved
        return frozen

    def substituted(self, node, old, new):
        """The node with one name replaced, for reading off the instance."""
        if self.term(node) == old:
            return _Literal(new)
        if not node.children:
            return node
        return Node(node.notation, node.sort,
                    [self.substituted(c, old, new) for c in node.children],
                    node.text)


class _Literal:
    """A term already in kernel form, standing in a tree."""
    notation, sort, children, text = 'literal', None, (), ''

    def __init__(self, term):
        self.term = term


def corpus(root):
    records = []
    for path in sorted((root / 'db').glob('*.records')):
        rel = str(path.relative_to(root))
        records.extend(parse_database(rel, check_encoding(rel,
                                                          path.read_bytes())))
    theorems = []
    for path in sorted((root / 'proof').glob('*.proof')):
        rel = str(path.relative_to(root))
        theorems.extend(parse_proof(rel, check_encoding(rel,
                                                        path.read_bytes())))
    return records, theorems


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
    variable would not be eliminable."""
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
    the header is written would count those too."""
    digest = hashlib.sha256(Path(path).read_bytes()).hexdigest()
    print(f'   Checked against a set.mm of {count:,} assertions, sha256')
    print(f'   {digest}. $)')


def write_definitions(records, sigs, setmm):
    """The corpus's definitions, as a file the proofs include."""
    said = definitions(records, sigs)
    print('$( definitions, from db/items.records by parley/elaborate.py.')
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


def render(rpn, sigs):
    """A term written the way a Metamath file writes it.

    A proof is reverse Polish because that is what the kernel reads, and a
    `$a` states its claim in full, so anything the elaborator writes out has
    to come back the other way."""
    stack = []
    for token in rpn.split():
        sig = sigs[token]
        count = len(sig.floats)
        args = stack[len(stack) - count:] if count else []
        del stack[len(stack) - count:]
        bound = dict(zip(sig.push, args, strict=True))
        stack.append(' '.join(bound.get(t, t) for t in sig.statement[1:]))
    return stack[0]


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


def main(argv):
    if len(argv) < 3:
        print(__doc__.strip().splitlines()[-1], file=sys.stderr)
        return 2
    wanted, setmm = argv[1], argv[2]
    root = Path(__file__).resolve().parent.parent
    records, theorems = corpus(root)
    if wanted == '--definitions':
        return write_definitions(records, read_library(setmm), setmm)
    grammar = Grammar.load(records)
    items = {r.name: r for r in records
             if r.kind in ('definition', 'theorem')}
    found = [t for t in theorems if t.name == wanted]
    if not found:
        print(f'no theorem {wanted!r}', file=sys.stderr)
        return 2
    thm = found[0]
    sorts_in_scope(thm, grammar)
    # What this corpus proves below the readable layer is read alongside the
    # library, so a `target` may name one of its labels exactly as it names
    # a set.mm label. The file is generated, and a proof that cites nothing
    # in it elaborates whether or not it has been built.
    supplied = path_of('geometry')
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

    work = Elaborator(thm, grammar, items, sigs, records, theorems)
    goal, hypotheses, proof = work.run()
    antecedent = hypotheses[0] if hypotheses else None
    for extra in hypotheses[1:]:
        antecedent = seq(antecedent, extra, 'wa')
    if antecedent is None:
        # Nothing is assumed, so the scope that carried the proof was truth
        # and the statement says only what the theorem concludes.
        proof = seq(goal, proof, 'mptru')

    print(f'$( {thm.name}, elaborated from {thm.path} by parley/elaborate.py.')
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
    # the library: one chain rather than one per proof.
    for name in work.cited:
        print(f'$[ {name}.mm $]')
    if not work.cited:
        # geometry.mm includes the definitions, so a proof that reaches one
        # of its labels needs only the one include; a proof that reaches
        # none does not read it at all.
        wants = provided & set(proof.split())
        print(f'$[ {"geometry" if wants else "definitions"}.mm $]')
    print()
    for label, statement in work.axioms:
        print(f'{label} $a {statement} $.')
    if work.axioms:
        print()
    # Every variable the proof touches has to be disjoint from every other:
    # the lemmas that discharge a scope want the bound name apart from what
    # the theorem is about, and there is nothing here for them to collide in.
    bound = sorted({sigs[t].statement[1] for t in set(proof.split())
                    if t in sigs and sigs[t].kind == '$f'})
    print('${')
    if len(bound) > 1:
        print('  $d ' + ' '.join(bound) + ' $.')
    label = label_of(thm.name, sigs)
    says = (f'( {work.render(antecedent)} -> {work.render(goal)} )'
            if antecedent else work.render(goal))
    print(f'  {label} $p |- {says} $=')
    print(f'    {proof} $.')
    print('$}')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))

