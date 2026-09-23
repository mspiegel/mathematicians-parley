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
import contextlib
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
from compress import compress
from formula import Grammar, Node, parse
from library import Signature
from library import read as read_library
from match import binding_context, instantiation, match
from match import names as names_in
from parse import (
    NAME,
    Declined,
    Problem,
    Theorem,
    citations,
    corpus,
    declined,
    fmt,
)
from sorts import sorts_in_scope, sorts_of_record, sorts_of_statement
from spell import Builder, Proof, seq

LABEL = re.compile(r'\s*\([A-Z]+[0-9]*\)\s*$')
# `let A be a set` introduces a name the way `let n ∈ ℕ` does, and states
# what `A is a set` states. The hypothesis line reads better as it is
# written; the claim is the notation the database declares. Points are the
# same shape, and every sort with a notation could be.
BE_A = re.compile(r'\s+be\s+a\s+(set|point)\b')
# Past the last line any proof has, for reading every define that is left.
_ENDLESS = float('inf')
CLASS_NAMES = ['cA', 'cB', 'cC', 'cD', 'cE', 'cF', 'cG', 'cH']
# Variables for a name the proof does not spell: what a `define` renames
# its body's binders to, and what an `obtain` introduces. A name the text
# does spell keeps its own letter, so this holds what a reader is least
# likely to write, and holds enough of them that a proof binding several
# names of its own does not run the list out.
SPARE_VARS = ['vm', 'vk', 'vj', 'vi', 'vp', 'vq', 'vr', 'vs', 'vt', 'vu',
              'vo', 'vl', 'vg', 'vh', 'vf', 'vw', 'vv']
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


REQUIRES = 'requires@'


def requirement(line):
    """What a `requires` line is called as the origin of a proof.

    It has no number of its own, so it is named by where it stands.
    """
    return f'{REQUIRES}{line}'


def from_requires(proof):
    """Whether a `requires` line made this proof."""
    return any(o.startswith(REQUIRES) for o in getattr(proof, 'origin', ()))
# How set.mm names that a digit belongs to a number system, by the system.
# The label is the digit and this suffix throughout — `2z`, `1nn`, `0re` —
# so what a system needs here is how its name is spelt in that label and
# nothing else.
SYSTEMS = {'cc': 'cn', 'cr': 're', 'cz': 'z', 'cn': 'nn', 'cn0': 'nn0',
           'cq': 'q'}
# The lemma that puts a sum, difference, product or power in a number system
# from its parts being there, by operator and system; a power's exponent is
# in ℕ₀ whatever the system. A compound's membership is built from its
# atoms' this way, so an atom's is the step's own line where it wrote one.
CLOSED = {
    ('caddc', 'cc'): 'addcld', ('cmin', 'cc'): 'subcld',
    ('cmul', 'cc'): 'mulcld', ('cexp', 'cc'): 'expcld',
    ('caddc', 'cr'): 'readdcld', ('cmin', 'cr'): 'resubcld',
    ('cmul', 'cr'): 'remulcld', ('cexp', 'cr'): 'reexpcld',
    ('caddc', 'cz'): 'zaddcld', ('cmin', 'cz'): 'zsubcld',
    ('cmul', 'cz'): 'zmulcld', ('cexp', 'cz'): 'zexpcld',
    ('caddc', 'cn'): 'nnaddcld', ('cmul', 'cn'): 'nnmulcld',
    ('caddc', 'cn0'): 'nn0addcld', ('cmul', 'cn0'): 'nn0mulcld',
    ('cexp', 'cn0'): 'nn0expcld',
}
NEGATED = {'cc': 'negcld', 'cr': 'renegcld', 'cz': 'znegcld'}




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
    the other is the two saying the same thing at different scales.
    """
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


def multiplier(shape, scale):
    """The term a combination multiplies one cited equation by, or None.

    `field.spell` writes the canonical polynomial, which raises an atom to
    the first power and multiplies it by one. That is what two polynomials
    being compared want and not what a factor wants: `( -u 1 x. ( q ^ 1 ) )`
    asks for two memberships nothing declares where `-u q` asks for one that
    is. So a multiplier is written the short way.
    """
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
    wants a digit, because nothing here has to spell the scalar.
    """
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
    happens here and every reader of a hypothesis gets it.
    """
    body = text[len(kind):] if text.startswith(kind) else text
    if kind == 'let':
        body = BE_A.sub(lambda m: f' is a {m.group(1)}', body)
    return body


def label_of(name, taken=(), path='', line=0):
    """What this elaborator calls a theorem it has written out.

    set.mm proves some of what this corpus proves and has its own names for
    them, so the label is moved off any that is already in use: `sqrt2irr`
    is taken. Which name it lands on depends only on set.mm, so a theorem
    that cites another agrees with the file that wrote it.

    Where it runs out of names the theorem is the thing to rename, so its
    own place is what the defect carries. This is the one defect outside
    `Elaborator`, which is why it is passed rather than known.
    """
    stem = name.replace('-', '')[:8]
    if stem not in taken:
        return stem
    for digit in range(1, 10):
        moved = f'{stem[:7]}{digit}'
        if moved not in taken:
            return moved
    raise Problem(path, line, f'no free label near {stem!r}')


class Fact:
    """A claim, a proof of it at one scope, and the sentences it was read from.

    A line may say several things, and a substitution may land in one of
    them, so what is kept is every sentence rather than the claim as one
    tree. A line read from no text at all keeps none.
    """

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
        self.bound = None           # and which variable each binder had
        self.inner = None           # and which each had while it was open
        self.assumed = {}           # cases: part number -> what it assumes
        self.entered = None         # cases: the part now open
        self.case_opened_at = None  # cases: the closers before that part
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
        ('cpw', (0,)): 'pweqd', ('csn', (0,)): 'sneqd',
        ('cun', (0,)): 'uneq1d', ('cun', (1,)): 'uneq2d',
        ('cun', (0, 1)): 'uneq12d',
        ('cdif', (0,)): 'difeq1d', ('cdif', (1,)): 'difeq2d',
        ('cdif', (0, 1)): 'difeq12d',
        ('cin', (0,)): 'ineq1d', ('cin', (1,)): 'ineq2d',
        ('cin', (0, 1)): 'ineq12d',
        ('wss', (0,)): 'sseq1d', ('wss', (1,)): 'sseq2d',
        ('wss', (0, 1)): 'sseq12d',
        ('wa', (0,)): 'anbi1d', ('wa', (1,)): 'anbi2d',
        ('wa', (0, 1)): 'anbi12d',
        ('w3a', (0,)): '3anbi1d', ('w3a', (1,)): '3anbi2d',
        ('w3a', (2,)): '3anbi3d', ('w3a', (0, 1, 2)): '3anbi123d',
        ('wn', (0,)): 'notbid',
        # A universal over an `if ... then` changes both sides at once when
        # the name it binds stands on each of them.
        ('wi', (0,)): 'imbi1d', ('wi', (1,)): 'imbi2d',
        ('wi', (0, 1)): 'imbi12d',
        ('wral', (0,)): 'ralbidv', ('wrex', (0,)): 'rexbidv',
        # And the same over every set there is, which a `let X be a set`
        # quantifies and the subsets proof inducts under.
        ('wal', (0,)): 'albidv'}

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
        self.combined = {}           # by step line, what its method combined
        self.sorts = frozenset()     # labels of set, point and function lines
        self.defines = frozenset()   # labels of `define` lines
        self.written = {}        # side conditions the step being proved wrote
        self.saying = set()      # terms `said_otherwise` is working on now
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

    # --- terms --------------------------------------------------------------

    @contextlib.contextmanager
    def in_its_names(self, item):
        """The sorts an item's own lines state, while its lines are read.

        A name is what says which of two notations sharing a pattern is
        meant, and `|_|` is cardinality or absolute value according to what
        stands inside it. The names in scope are the proof's; an item's
        hypotheses are written in its own, and `let Y be a set` is where it
        says so.
        """
        kept = self.g.sorts
        own = (sorts_of_statement(item) if isinstance(item, Theorem)
               else sorts_of_record(item))
        self.g.sorts = {**kept, **own}
        try:
            yield
        finally:
            self.g.sorts = kept

    def read(self, text):
        """One sentence of the readable layer, as a tree.

        Where the elaborator has got to goes with it. A formula that does
        not parse is a defect and wants somewhere to point; without a
        position it arrived looking like a route declining, and a `requires`
        line nobody could read was taken as stated instead of reported.
        """
        return parse(LABEL.sub('', text).strip(), self.g,
                     self.thm.path, self.at)

    def term(self, node):
        if node.notation == 'literal':
            return node.term
        if node.notation == 'name':
            if node.text not in self.names:
                # A name the proof never introduced, which is the text's to
                # fix wherever the reading of it came from.
                raise self.defect(self.at,
                                  f'no kernel name for {node.text!r}')
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
        what being local to a definition means.
        """
        out = {}
        for name in targets.fixes(self.pattern(node)):
            if name not in self.fixed:
                raise self.defect(self.at,
                                  f'notation {node.notation!r} is about '
                                  f'{name!r}, which this theorem does not fix')
            out[name] = self.fixed[name]
        return out

    def spelling(self, node):
        """The node's target with what it holds fixed already resolved.

        A shape is read from this rather than from the target as written,
        because a fixed name is a term of the theorem's and not a hole: a
        rewrite walks past it the way it walks past a constant.
        """
        pattern, fixed = self.pattern(node), self.held(node)
        return (targets.FIXED.sub(lambda m: fixed[m.group(1)], pattern)
                if fixed else pattern)

    def pattern(self, node):
        """The `target` entry of the pattern this node was built from.

        A notation with no target is a gap in `db/notation.records` and so
        a person's to fix. The position is the line that wrote the notation
        rather than the record that fails to declare it, because that is the
        one this knows and it is where a reader would start looking.
        """
        entries = self.terms.get(node.notation)
        if entries is None:
            raise self.defect(self.at,
                              f'notation {node.notation!r} has no target field')
        order = self.literals.get(node.notation, [])
        found = entries[order.index(node.text)] if node.text in order \
            else entries[0]
        if found is None:
            raise self.defect(self.at,
                              f'notation {node.notation!r} builds no term here')
        return found

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

    def settle(self, wanted, scope, facts, depth=7, step=None, lines=None):
        """A proof of something a step needs and the text does not write.

        `depth` bounds the chain, and seven is what the deepest one in the
        corpus costs: a power set is finite because its size is a natural
        number, which is a power of two, whose base is two. Each of those is
        a declared lemma asking the next, and a shorter bound stopped that
        chain rather than any search. It is not free — six costs
        `least-combination-divides` 27 seconds to elaborate and eight costs
        it 37 — so it is the depth that was measured, not a round number.

        A cited lemma asks side conditions of its own — that an index is in
        the upper integers, that a summand is complex — and those are not
        `requires` lines, because to a reader they are not steps. They are
        settled from the lemmas `targets.MEMBERSHIP` names, by matching what
        each concludes against what is wanted.

        A step is passed only where one is there to have cited a witness,
        which is what lets an existential be proved at all. Side conditions
        pass none, so they stay what they are: settled from declared
        lemmas, never by finding a fact that happens to fit.
        """
        rpn = wanted.rpn(self.flabel)
        if rpn in facts:
            return facts[rpn]
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
        if wanted.label in self.BOUND:
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
                lambda one: self.settle(one, scope, facts, depth - 1, step,
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
                # Going under the binder spends no depth. It is one claim
                # said of one member, not a step of the chain the bound is
                # there to cut off, and spending it stopped `f1mpt` halfway.
                # Conjunction still spends: doing both cost
                # `least-combination-divides` sixty seconds and bought
                # nothing.
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
                for label in targets.MEMBERSHIP:
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
        return self.no('cannot settle {}', rpn)

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
        for label in targets.MEMBERSHIP:
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
                # A class neither the claim nor a fact fixes is set.mm asking
                # where to look for the thing rather than asking anything of
                # it, which `apply_lemma` reads the same way: `pwexg` wants a
                # class holding the set whose power class is about to be one,
                # and _V holds every set. What is left is then settled.
                for open_slot in self.sethood(slot, binding):
                    binding[open_slot] = kernel.Term('cvv')

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
            first = proof.text.split()[-1] == label
            fold = self.DISCHARGE[(joins[i], first)]
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
            if token in WRAPS and args[-1][0] == 'const':
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
        moved = [x for slot in slots for x in (was[slot], now[slot])]
        rest = [o for j, o in enumerate(was) if j not in slots]
        built = self.seq(*now, label, wrap) if wrap else self.seq(*now, label)
        return built, self.seq(scope, *moved, *rest, label if wrap else '',
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
        way the text writes it.
        """
        item = self.items[name.split(':', 1)[1]]
        lemma, flipped = targets.unfolding(item)
        if lemma is None:
            raise self.defect(self.at,
                              f'{name} has no target field')
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
        # of them: `thm:lowest-terms` exhibits a p and a q that one line
        # says are a fraction in lowest terms, another says is positive,
        # and a third says nothing divides. Where it is all of it, its own
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
        """
        for text in sig.essentials:
            asked = self.syntax.parse(text[1:], 'wff')
            if asked.label != 'wceq' or len(asked.children) != 2:
                continue
            name = asked.children[0].variable
            if name is None or name not in binding:
                continue
            said = kernel.match(asked.children[1], binding[name],
                                dict(binding), variables)
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

    # Lifting a closed biconditional through one level of a term. The
    # deduction forms `congruence` uses take the scope as an antecedent;
    # these take nothing, which is what a renaming needs.
    RENAMED: typing.ClassVar = {('wa', (0,)): 'anbi1i', ('wa', (1,)): 'anbi2i',
                                ('wi', (0,)): 'imbi1i', ('wi', (1,)): 'imbi2i'}

    # One binder: the lemma that changes what it binds over, and the one
    # that changes the name it binds. Both closed, and the `w` on the
    # second is set.mm's version that does not lean on ax-13.
    BOUND: typing.ClassVar = {'wrex': ('rexbii', 'cbvrexvw'),
                              'wral': ('ralbii', 'cbvralvw'),
                              'wal': ('albii', 'cbvalvw')}

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
        under = self.BOUND.get(given.label)
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
            label = self.RENAMED.get((given.label, (slot,)))
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

    def congruence(self, given, want, scope, facts, step, leaf):
        """Carry one change up to the whole term it sits in.

        Two terms that differ in one place are walked in step, and the
        lemma that lifts each level is the one the tree names: the walk
        `descend` makes over a readable claim, made here over a term the
        kernel holds. What counts as the change, and what proves it there,
        is the caller's.

        What it refuses is a route declining and not a defect, however it
        was reached. It used to carry the step's line where a caller had a
        step and none where one did not, so the same failure was a defect
        or a decline according to who was on the stack.
        """
        found = leaf(given, want, scope, facts)
        if found is not None:
            return found
        if (given.label != want.label
                or len(given.children) != len(want.children)):
            return self.no(
                '{} and {} differ by more than the change being carried',
                given.rpn(self.flabel), want.rpn(self.flabel))
        if given.label == 'wrex':
            body, variable, over = given.children
            name, runs = variable.rpn(self.flabel), over.rpn(self.flabel)
            member = self.seq(f'{name} cv', runs, 'wcel')
            # The scope under a binder belongs to the walk and to nothing
            # else. `widen` keeps a frame so that a step whose lemma forbids
            # an assumption can be proved without it, and a frame left
            # standing here is offered to whatever is proved next: a lemma
            # chose one and stated its hypothesis under a binder's
            # membership, which mmverify is what caught.
            frame = len(self.frames)
            inner, lifted = self.widen(scope, facts, member)
            made = self.congruence(body, want.children[0], inner, lifted,
                                   step, leaf)
            del self.frames[frame:]
            if declined(made):
                return made
            return self.seq(scope, body.rpn(self.flabel),
                       want.children[0].rpn(self.flabel), name, runs, made,
                       'rexbidva')
        wrapped = given.label in WRAPS
        kids = given.children[:-1] if wrapped else given.children
        wants = want.children[:-1] if wrapped else want.children
        spelt = [c.rpn(self.flabel) for c in kids]
        other = [c.rpn(self.flabel) for c in wants]
        slots = [i for i in range(len(kids)) if spelt[i] != other[i]]
        if not slots:
            return Declined('nothing changed under this term')
        moved = [x for i in slots for x in (spelt[i], other[i])]
        rest = [s for i, s in enumerate(spelt) if i not in slots]
        head = given.children[-1].rpn(self.flabel) if wrapped else ''
        under = [self.congruence(kids[i], wants[i], scope, facts, step, leaf)
                 for i in slots]
        for one in under:
            if declined(one):
                return one
        return self.seq(scope, *moved, *rest, head, *under,
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
        text writes them.
        """
        said = [self.term(self.read(s)) for s in self.sentences(text)]
        whole = said[0]
        for extra in said[1:]:
            whole = self.seq(whole, extra, 'wa')
        return whole

    def hypotheses(self):
        """Name every `let` variable, and read the hypotheses.

        A `let` introduces a name and says what it ranges over. `let n ∈ ℕ`
        says it with a membership, `let A be a set` with no set at all, and
        `let f : A → 𝒫A` by saying what the name maps between. All three
        name the thing they introduce first, so all three are read the same
        way: name the leftmost leaf, then read the line as a claim about
        it.
        """
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
        them.
        """
        while self.unread < len(self.thm.defines):
            _kind, text, label, line = self.thm.defines[self.unread]
            if line >= before:
                return
            self.unread += 1
            said = LABEL.sub('', text[len('define'):]).strip()
            name, _, body = said.partition(':=')
            name = name.strip()
            if not body.strip():
                raise self.defect(line, f'define {label} says nothing')
            if name in self.names:
                raise self.defect(line, f'{name} is already named')
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
        make the definition speak of some other element.
        """
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

    def unproved_requires(self):
        """The `requires` lines of this theorem never proved from their reasons.

        A `requires` line is where a step writes a side condition and why it
        holds, and each is proved from that reason once, when its step
        starts, and checked then to rest on nothing else. A line never
        proved is one whose reason nothing checked: what it says may have
        been reached some other way, or not been needed, and either way the
        page's justification went unread. Every line of every step, whatever
        it cites.
        """
        return sorted(line for step in self.thm.steps
                      for _text, _how, line in step.requires
                      if requirement(line) not in self.rests_on)

    def widen(self, scope, facts, added, origin=None):
        """Conjoin one more thing onto the antecedent, carrying the facts.

        This is what every block form does when it opens: `ELABORATION.md`
        requirement 1. The frame is kept so that a step whose lemma forbids
        the innermost assumption can be proved without it.

        `origin` is what on the page the assumption is, where it is on the
        page at all. A block's supposition is; the membership of a variable
        a binder introduces while its body is read is not, and has none.
        """
        inner = seq(scope, added, 'wa')
        lifted = {k: self.seq(inner, scope, k,
                              self.seq(scope, added, 'simpl'), v, 'syl')
                  for k, v in facts.items()}
        lifted[added] = self.seq(scope, added, 'simpr')
        if origin is not None:
            lifted[added] = self.seal(lifted[added], origin)
        self.unpack(added, lifted[added], inner, lifted)
        # Each frame keeps what is known at it, because a step whose lemma
        # forbids an inner assumption is proved at an outer one.
        self.frames.append((inner, added, lifted))
        return inner, lifted

    def lifted_to(self, claim, proof, at, scope):
        """A proof made under `at`, said under `scope`, if `scope` is `at`
        widened; None otherwise.

        Every widening conjoins one assumption onto the antecedent, so a
        scope opened inside another reads back as that one with each added
        assumption hanging off it, and the proof is carried in the way
        `widen` carries every fact: one `simpl` and `syl` per assumption.
        A scope that is not a widening of `at` — one a step was hoisted to —
        gives None, and the proof made under `at` is not offered there.
        """
        if at == scope:
            return proof
        chain, node = [], self.to_term(scope)
        while node.variable is None and node.label == 'wa' \
                and len(node.children) == 2:
            outer, added = node.children
            chain.append(added.rpn(self.flabel))
            if outer.rpn(self.flabel) == at:
                break
            node = outer
        else:
            return None
        here = at
        for added in reversed(chain):
            inner = self.seq(here, added, 'wa')
            proof = self.seq(inner, here, claim, self.seq(here, added, 'simpl'), proof,
                        'syl')
            here = inner
        return proof if here == scope else None

    ARITHMETIC = frozenset({'caddc', 'cmin', 'cmul', 'cdiv'})
    RELATIONS = frozenset({'wceq', 'wne', 'wbr', 'wn', 'wa'})

    def atoms_of(self, rpn, atoms, terms):
        """The atoms of a claim a method combined, and every term in it.

        An atom is what the method treats as a number it knows nothing
        about: a name, an absolute value, a function's value, a power whose
        exponent is not a numeral. Sums, differences, products, quotients,
        negations and numeral powers are looked inside; numerals are not
        atoms. `METHODS.md`: each atom is a real number, which the step
        writes or cites.
        """
        def walk(node):
            if node.variable is None and node.label in self.RELATIONS:
                kids = node.children[:2] if node.label == 'wbr' \
                    else node.children
                for kid in kids:
                    walk(kid)
                return
            terms.add(node.rpn(self.flabel))
            if linear.numeral(node, self.flabel) is not None:
                return
            if node.variable is None and node.label == 'co' \
                    and len(node.children) == 3:
                op = node.children[2].rpn(self.flabel)
                if op in self.ARITHMETIC:
                    walk(node.children[0])
                    walk(node.children[1])
                    return
                if op == 'cexp' and linear.numeral(
                        node.children[1], self.flabel) is not None:
                    walk(node.children[0])
                    return
            if node.variable is None and node.label == 'cneg':
                walk(node.children[0])
                return
            atoms.add(node.rpn(self.flabel))
        walk(self.to_term(rpn))

    def does_work(self, step, number, proof):
        """Everything a step names does work, or a defect names what does not.

        A cited line or requires line is at work where the proof rests on it,
        directly or through another of the step's requires lines. On a
        method step a requires line is also at work where the method demands
        it without the kernel needing it — a membership of an atom of what
        was combined, a term of it not zero — and each such atom's membership
        must be on the page. A step citing an item is the checker's to judge,
        since the item's statement says what it asks.
        """
        head = step.just.head if step.just else ''
        if head.startswith(('def:', 'thm:')):
            return
        used = set(getattr(proof, 'origin', ()))
        todo = [u for u in used if u.startswith(REQUIRES)]
        while todo:
            for more in self.rests_on.get(todo.pop(), ()):
                if more not in used:
                    used.add(more)
                    if more.startswith(REQUIRES):
                        todo.append(more)
        for ref in dict.fromkeys(step.just.refs):
            if ref not in used and ref not in self.defines \
                    and ref not in self.sorts:
                raise self.defect(step.line, f'step {number} cites {ref} and '
                                             f'uses nothing it says')
        atoms, terms = set(), set()
        for claim in self.combined.get(step.line, ()):
            self.atoms_of(claim, atoms, terms)
        written = {}
        for text, _how, line in step.requires:
            claim = self.to_term(self.term(self.read(text)))
            written[line] = claim
            if requirement(line) in used:
                continue
            if claim.label == 'wcel':
                demanded = claim.children[0].rpn(self.flabel) in atoms
            elif claim.label == 'wne':
                demanded = claim.children[0].rpn(self.flabel) in terms
            elif claim.label == 'wn' and claim.children[0].label == 'wceq':
                demanded = claim.children[0].children[0].rpn(
                    self.flabel) in terms
            else:
                demanded = False
            if not demanded:
                raise self.defect(line, f'the requires line of step {number} '
                                        f'says {text.strip()}, and the step '
                                        f'neither uses nor asks for it')
        cited = {part for ref in step.just.refs if ref in self.lines
                 for part in self.parts(self.lines[ref].term)}
        for atom in sorted(atoms):
            said = any(c.label == 'wcel' and c.children[0].rpn(self.flabel)
                       == atom for c in written.values())
            said = said or any(
                self.to_term(p).label == 'wcel'
                and self.to_term(p).children[0].rpn(self.flabel) == atom
                for p in cited)
            if not said:
                # By the name the page writes, where the atom is one.
                shown = next((name for name, kernel in self.names.items()
                              if kernel == atom), self.render(atom))
                raise self.defect(step.line,
                                  f'step {number} combines {shown}, and '
                                  f'nothing it writes or cites says it is a '
                                  f'number')

    def combining(self, *terms):
        """Record what a method step's claim is built from.

        The claim and the sentences of cited lines the method combined —
        which the certificate says, not every sentence a cited line says.
        `METHODS.md`: an atom is one of these, and each is real.
        """
        self.combined.setdefault(self.at, set()).update(terms)

    def named(self, step, number, block=False):
        """What a step names, which is everything its proof may rest on.

        The lines it cites and its own requires lines, and the sorts in
        scope. A block also rests on its own steps and on what it assumes,
        and on the lines a `join` inside it names: a join that closes a
        contradiction emits nothing, and the block's close uses what it
        joined (`ELABORATION.md` requirement 8).
        """
        out = (set(step.just.refs) - self.defines) | self.sorts
        out |= {requirement(line) for _t, _h, line in step.requires}
        if block:
            out |= {k for k in self.lines if k.startswith(number + '.')}
            out |= {o[2] for o in step.openers if o[2]}
            out.add(f'{number} assumes')
            depth = number.count('.') + 1
            for inner in self.thm.steps:
                name = '.'.join(str(p) for p in inner.number)
                if name.startswith(number + '.') \
                        and name.count('.') == depth \
                        and inner.just.head == 'join':
                    out |= set(inner.just.refs) - self.defines
        return out

    def discharged_by(self, made, step, how, line):
        """A requires line's proof, checked against its reason and sealed.

        It rests only on the lines its reason cites, the step's other
        requires lines, which `check.py` also lets one line discharge from
        another, and the sorts in scope.
        """
        allowed = set(citations(how)) | self.sorts
        allowed |= {requirement(one) for _t, _h, one in step.requires}
        self.rests_on_named(made, allowed, line, 'the requires line')
        return self.seal(made, requirement(line))

    def rests_on_named(self, proof, allowed, line, what):
        """A proof resting on nothing its line does not name, or a defect.

        `GOALS.md` decision 9: the kernel proof is derived from the text, so
        what it rests on is what the text says it rests on. A proof that
        verifies while resting on something else says nothing is wrong, and
        this is where that is said.
        """
        extra = sorted(getattr(proof, 'origin', frozenset()) - allowed)
        if extra:
            shown = ', '.join(f'the requires line at {e[len(REQUIRES):]}'
                              if e.startswith(REQUIRES) else e for e in extra)
            raise self.defect(line, f'{what} rests on {shown}, which it does '
                                    f'not name')

    def seal(self, proof, item):
        """The proof, standing from here on for one thing on the page.

        What a later step builds from it rests on `item` and not on whatever
        `item` was itself built from, which is the question each step is
        asked about: what it names against what it used. What the proof was
        built from is kept in `rests_on`, which is how a line is asked the
        same of its own reason, and how a line's uses are traced through the
        lines that use it.
        """
        self.rests_on[item] = (self.rests_on.get(item, frozenset())
                               | getattr(proof, 'origin', frozenset()))
        return Proof(proof.text, {item})

    # A fact that conjoins several things says each of them, and the steps
    # below cite them one at a time: an `obtain` hands over one body saying
    # that q is positive, that x is p over q, and that nothing divides both.
    SPLIT: typing.ClassVar = {'wa': ('simpl', 'simpr'),
                              'w3a': ('simp1', 'simp2', 'simp3')}
    # And the other direction: what conjoins a proof of each part into a
    # proof of the whole. `SPLIT` is read where a fact is taken apart and
    # this where a goal is put together, and both are asked by label so
    # that a shape neither names is left alone.
    JOIN: typing.ClassVar = {'wa': 'jca', 'w3a': '3jca'}

    def conjoined(self, wanted, scope, answer):
        """A conjunctive goal, from whatever answers each of its parts.

        Both places that reach a conjunction want the same three moves —
        take the parts, answer each, join what comes back — and differ only
        in what answering is: `settle` proves a part from the scope, and
        `required` reads the line the step wrote for it. So the moves are
        here and the answering is the caller's.

        None where the goal is not one of these shapes, which is not a
        decline: the caller has its own way on and this had no opinion.
        """
        if wanted.label not in self.JOIN:
            return None
        under = [answer(one) for one in wanted.children]
        for one in under:
            if declined(one):
                return one
        return self.seq(scope, *(one.rpn(self.flabel) for one in wanted.children),
                   *under, self.JOIN[wanted.label])

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
            facts[part] = self.seq(scope, term, part, proof, *kids, pick, 'syl')
            self.unpack(part, facts[part], scope, facts, depth - 1)

    def open_block(self, step, scope, facts, lines):
        """A block's assumption is conjoined onto the antecedent.

        All four block forms do this; what differs is the lemma that closes
        them. `ELABORATION.md` requirement 1.
        """
        head = step.just.head
        block = Block(step, scope, facts, len(self.frames) - 1)
        # Taken before the block names anything, so that what it names is
        # what closing it gives back.
        block.named, block.bound = dict(self.names), dict(self.bound_as)
        if head == 'contradiction':
            kind, text, label, _l, _p = step.openers[0]
            node = self.read(hypothesis_body(kind, text))
            block.supposed = self.term(node)
            block.scope, block.facts = self.widen(
                scope, facts, block.supposed, self.assumption(block, label))
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
                    block.variable = self.fixed_var(name, block.scope)
                    self.names[name] = f'{block.variable} cv'
                    # `let X be a set` fixes a name over nothing and says
                    # only that it is a set, so there is no set to record,
                    # the same way `hypotheses` reads it at the head.
                    if node.notation == 'membership':
                        self.sets[name] = self.term(node.children[1])
                node = self.read(body)
                added = self.term(node)
                block.scope, block.facts = self.widen(
                    block.scope, block.facts, added,
                    self.assumption(block, label))
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
            raise self.defect(step.line,
                              f'no expansion for a {head} block')
        return block

    @staticmethod
    def assumption(block, label):
        """What on the page a block's assumption is.

        Its label where the text gives one. Where it does not, the block's
        own step, since that is where a reader finds it; an assumption with
        no name is still something the page says, and a proof resting on it
        rests on the page rather than on nothing.
        """
        if label:
            return label
        return '.'.join(str(p) for p in block.owner.number) + ' assumes'

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
                                              assumed,
                                              self.assumption(block, label))
        block.entered = part
        if label:
            lines[label] = Fact(assumed, block.facts[assumed], (node,))
        return block.scope, block.facts

    @staticmethod
    def end_case(block, closers):
        """The closers an obtain raised inside a case, spent where it ends.

        The lemma that closes the cases wants each case over the scope the
        case opened, and an obtain inside one widens that: the first case
        of the intermediate value proof obtains δ and then x₁. So what the
        case ends on is discharged of them, as a contradiction's claim is.
        """
        if block.case_opened_at is None:
            return closers
        inside = closers[block.case_opened_at:]
        if inside and block.entered in block.parts:
            claim, proof, _where = block.parts[block.entered]
            for close in reversed(inside):
                proof = close(proof, claim)
            block.parts[block.entered] = (claim, proof, block.scope)
        return closers[:block.case_opened_at]

    @staticmethod
    def hand_up(done, blocks):
        """A closed block is the result of the part of its parent it sits in.

        What it was proved under goes up with it, because a part's claim is
        written inside the part and what reads it stands outside.
        """
        if done.owner.part is not None and blocks:
            blocks[-1].parts[done.owner.part] = (done.claim, done.proof,
                                                 done.outer)
            if done.variable:
                blocks[-1].variable = done.variable

    def close_block(self, block, facts, lines, closers, deep):
        """What a block gives back, by the lemma its kind closes with.

        An `obtain` inside a block does not discharge where the proof ends:
        it discharges where the block does, since the lemma that closes the
        block wants what the block holds and not what the obtain's scope
        holds. So the closers raised inside a contradiction are spent on it,
        and only what is left over reaches the end of the proof.
        """
        step = block.owner
        head = step.just.head
        inside = closers[block.opened_at:]
        # A block gives back its scope and its names together: the frames it
        # pushed, and whatever it fixed, obtained or defined inside. The
        # word a fixed name took goes back with them, so an enclosing block
        # that binds the same word still means what it meant.
        block.inner = dict(self.bound_as)
        del self.frames[block.frame + 1:]
        self.names, self.bound_as = dict(block.named), dict(block.bound)
        if head == 'contradiction':
            block.claim, block.proof = self.close_contradiction(
                block, facts, inside, deep, lines)
            closers = closers[:block.opened_at]
        elif head == 'fix':
            held = lines[self.last]
            # A fix is a generalisation: it fixed a name, said something
            # about it, and the block claims that of every such name. It
            # closes the same way wherever it stands, including as a part
            # of an induction — what `nn0indd` wants of its step is not
            # what the block claims, and turning one into the other is
            # `close_induction`'s, since that is what knows the lemma.
            block.claim, block.proof = self.close_fix(block, held, inside)
            closers = closers[:block.opened_at]
        elif head == 'cases':
            closers = self.end_case(block, closers)
            block.claim, block.proof = self.close_cases(block, lines)
        elif head == 'induction':
            block.claim, block.proof = self.close_induction(block, lines)
        number = '.'.join(str(p) for p in step.number)
        self.rests_on_named(block.proof, self.named(step, number, block=True),
                            step.line, f'step {number}')
        self.does_work(step, number, block.proof)
        block.proof = self.seal(block.proof, number)
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
        between the lines whole.
        """
        step, scope, supposed = block.owner, block.outer, block.supposed
        if not self.joined:
            raise self.defect(step.line, 'the block closes on no join')
        held = lines.get(self.last)
        found = self.opposing([*self.joined,
                               *([held.term] if held else [])], facts, deep)
        if found is None:
            raise self.defect(step.line,
                              'the joined lines are not a contradiction')
        first, second, known = found
        claim = self.claim_of(' '.join(step.claim))
        proof = self.seq(deep, first, claim, known[first], known[second],
                    'pm2.21dd')
        for close in reversed(inside):
            proof = close(proof, claim)
        lifted = self.seq(scope, supposed, claim, proof, 'ex')
        if claim == self.seq(supposed, 'wn'):
            return claim, self.seq(scope, supposed, lifted, 'pm2.01d')
        if supposed == self.seq(claim, 'wn'):
            return claim, self.seq(scope, claim, lifted, 'pm2.18d')
        raise self.defect(step.line,
                          'the block claims neither its supposition negated '
                          'nor what its supposition denies')

    def opposing(self, lines, facts, scope):
        """A claim and its negation, among the parts of what the block holds.

        What holds the pair differs by proof: the √2 proof joins two lines
        that each say one thing, and Cantor's cases give back a single line
        saying both. So every part of every line offered is a candidate, and
        a line saying several things is taken apart first.
        """
        known = dict(facts)
        for line in lines:
            if line in known:
                self.unpack(line, known[line], scope, known)
        seen = [t for line in lines for t in self.parts(line) if t in known]
        for one in seen:
            for other in seen:
                if other == self.seq(one, 'wn'):
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
            return None
        return self.seq(scope, said, want, proof,
                   self.seq(self.seq(said, want, 'wb'), scope, apart, 'a1i'), 'mpbid')

    def close_fix(self, block, held, inside=()):
        """A fix closed by giving back everything it took.

        `ralrimiva` wants what was proved under a fixed name, said out of
        the scope the block opened over, and `ex` does the same for what
        the block assumed. `db/methods.records` names both, and a fix may
        take several names before it assumes: Bezout's step 10 fixes an x
        and a y and supposes their combination is a natural number.

        Which names, which sets and which supposition are read off the
        claim the block states, since that is what the text wrote, and they
        are peeled in the order the openers widened the scope. Putting them
        back runs the other way, innermost first, because that is the order
        each lemma can be applied in.

        A fix that is one part of an induction never arrives here:
        `close_block` hands that one over whole, for `nnind` to take.
        """
        step = block.owner
        # Read with the variables the block had, not the ones given back:
        # the claim quantifies the names the block fixed, and closing it
        # has already returned those words to whatever held them outside.
        kept, self.bound_as = self.bound_as, dict(block.inner)
        try:
            claim = self.claim_of(' '.join(step.claim))
        finally:
            self.bound_as = kept
        layers, rest = [], self.to_term(claim)
        for kind, _text, _label, _line, _part in step.openers:
            if kind == 'let' and rest.label == 'wral':
                body, variable, over = rest.children
                layers.append(('ralrimiva', variable.rpn(self.flabel),
                               over.rpn(self.flabel)))
                rest = body
            elif kind == 'let' and rest.label == 'wal':
                # `let X be a set` fixes a name over nothing, so the claim
                # says its body of every set there is and `alrimiv` gives
                # that back. `db/methods.records` names it beside the other.
                layers.append(('alrimiv',
                               rest.children[1].rpn(self.flabel), None))
                rest = rest.children[0]
            elif kind == 'assume' and rest.label == 'wi':
                layers.append(('ex', rest.children[0].rpn(self.flabel), None))
                rest = rest.children[1]
            elif kind == 'let':
                raise self.defect(
                    step.line, 'a fix that claims nothing of every such name')
            else:
                raise self.defect(
                    step.line, 'a fix whose claim supposes nothing where the '
                    'block assumes')
        # The scope each layer was taken at, which is what it is given back
        # to. `widen` conjoined them on the way in and these are the same
        # terms read off the claim.
        scopes, scope = [], block.outer
        for how, what, over in layers:
            scopes.append(scope)
            if how == 'ex':
                scope = self.seq(scope, what, 'wa')
            else:
                scope = self.seq(scope, self.seq(f'{what} cv', over or 'cvv', 'wcel'),
                            'wa')

        # An `obtain` inside the block widened the scope past what the
        # openers widened it to, and discharges where the block does, not
        # where the proof ends — the same as inside a contradiction. So the
        # closers it raised are spent before anything is generalised, and
        # what is left stands at the scope the openers made.
        proof, said = held.proof, held.term
        for close in reversed(inside):
            proof = close(proof, said)
        # The last line and the claim are written in different places, so a
        # name bound in both may be spelt two ways: the subsets induction's
        # step states what its own last line states, and that line was
        # written where the word was already taken.
        want = rest.rpn(self.flabel)
        proof = self.respelt(proof, said, want, scope)
        if proof is None:
            raise self.defect(step.line,
                              'the block does not reach what it claims of '
                              'the name it fixed')
        said = want
        for (how, what, over), outer in zip(reversed(layers),
                                            reversed(scopes), strict=True):
            if how == 'ex':
                proof = self.seq(outer, what, said, proof, 'ex')
                said = self.seq(what, said, 'wi')
            elif how == 'alrimiv':
                # `let X be a set` says X ∈ _V and the claim quantifies X
                # over nothing, so that membership is dropped before the
                # name is given back: every setvar is a set, which is `vex`.
                member = self.seq(f'{what} cv', 'cvv', 'wcel')
                proof = self.seq(outer, member, said, self.ap('vex', {'x': what}),
                            proof, 'mpan2')
                proof = self.seq(outer, said, what, proof, 'alrimiv')
                said = self.seq(said, what, 'wal')
            else:
                proof = self.seq(outer, said, what, over, proof, 'ralrimiva')
                said = self.seq(said, what, over, 'wral')
        return claim, proof

    def close_cases(self, block, lines):
        """The cases and the disjunction that says one of them holds.

        mpjaodan wants each case as an implication out of the scope with its
        own assumption conjoined, which is what each part was proved as, and
        the disjunction the block cites. The fourth and last block form, and
        the same shape as the other three: widen, prove, close with one
        lemma.

        More than two cases follow the disjunction, which is built from the
        left: `f(c) < 0 or f(c) = 0 or 0 < f(c)` is the first two or'd, then
        the third. `jaodan` makes one case of the first two, over their
        disjunction, and so on down, and `mpjaodan` closes on the last.
        """
        step, scope = block.owner, block.outer
        if set(block.parts) != set(block.assumed):
            raise self.defect(step.line, 'a case of the block proves nothing')
        claim = self.claim_of(' '.join(step.claim))
        parts = sorted(block.assumed)
        assumed = [self.term(block.assumed[p][0]) for p in parts]
        said = [block.parts[p][1] for p in parts]
        which, proof = assumed[0], said[0]
        for one, shown in zip(assumed[1:-1], said[1:-1], strict=True):
            proof = self.ap('jaodan', {'ph': scope, 'ps': which, 'ch': claim,
                                       'th': one}, proof, shown)
            which = seq(which, one, 'wo')
        disjunction = self.carried(step.just.refs[0], block.outside, lines)
        if seq(which, assumed[-1], 'wo') != self.lines[step.just.refs[0]].term:
            raise self.defect(step.line, 'the cases are not the disjunction '
                                         'the block cites, taken in order')
        return claim, self.ap('mpjaodan', {'ph': scope, 'ps': which,
                                           'ch': claim, 'th': assumed[-1]},
                              proof, said[-1], disjunction)

    def close_induction(self, block, lines):
        """Induction closes with the lemma for the set it runs over.

        Whichever it is wants the claim five ways and the text writes none
        of them: it says only which name to induct on and where to start. So
        the claim is read as a function of that name and instantiated, and
        each instance is tied to the general one by congruence.
        `ELABORATION.md` requirement 13.
        """
        step, scope = block.owner, block.outer
        if set(block.parts) != {0, 1}:
            raise self.defect(step.line, 'induction wants a base and a step')
        (base_claim, base, beneath), (step_claim, stepped, under) = (
            block.parts[0], block.parts[1])
        name, general = block.over, f'{block.base} cv'
        over = self.sets.get(name)
        if over not in INDUCTION:
            raise self.defect(step.line,
                              f'nothing here inducts over {self.render(over)}'
                              if over else
                              f'nothing says what {name} runs over')
        lemma, begins = INDUCTION[over]
        at = re.search(r'starting at ([^\s,]+)', step.just.text)
        start = self.term(self.read(at.group(1))) if at else begins
        if start != begins:
            raise self.defect(step.line,
                              f'an induction over {self.render(over)} starts '
                              f'at {self.render(begins)}, and the text says '
                              f'{self.render(start)}')
        variable = block.variable or self.spare_var()
        next_one = self.seq(f'{variable} cv', 'c1', 'caddc', 'co')

        saved = dict(self.names)
        self.names[name] = general
        # Read as a sentence, so that a claim written as prose ends where a
        # reader ends it: the subsets proof inducts on `For every set X, if
        # |X| = n then |𝒫X| = 2^n.`, and the stop is not part of the claim.
        #
        said = self.sentences(' '.join(step.claim))
        pattern = self.freeze(self.read(said[0] if len(said) == 1
                                        else ' '.join(step.claim)))
        self.names = saved
        shapes = [start, f'{variable} cv', next_one, self.names[name]]
        instances, ties = [], []
        for value in shapes:
            here = self.seq(general, value, 'wceq')
            built, proof = self.rewrite(pattern, general, value, here,
                                        self.seq(here, 'id'))
            instances.append(built)
            ties.append(proof)
        claimed, held, reached, whole = instances
        member = self.seq(self.names[name], self.sets[name], 'wcel')
        body = self.term(pattern)

        # A part gives back what it claims, and what a `fix` claims is a
        # universal. `nn0indd` asks its step as a deduction — the name and
        # the instance conjoined onto the scope — so the one is turned into
        # the other here, which is where the lemma is known.
        #
        # A part's claim is written inside the part, where a word may
        # already be taken by what the part assumes, so the subsets
        # induction's parts bind a set the pattern binds under another
        # letter. The same claim, and `respelt` says so. The step is put
        # into the lemma's spelling while it is still a universal, because
        # afterwards its hypothesis is in the scope, where a claim cannot
        # be respelt.
        taken = self.to_term(step_claim)
        if taken.label == 'wral' and taken.children[0].label == 'wi':
            says = self.seq(held, reached, 'wi')
            stepped = self.respelt(stepped, step_claim,
                                   self.seq(says, variable, over, 'wral'), under)
            if stepped is None:
                raise self.defect(step.line,
                                  'the step does not reach the next instance')
            inner = self.seq(under, self.seq(f'{variable} cv', over, 'wcel'), 'wa')
            stepped = self.seq(under, says, variable, over, stepped, 'r19.21bi')
            stepped = self.seq(inner, held, reached, stepped, 'imp')
            step_claim, under = reached, self.seq(inner, held, 'wa')

        base = self.respelt(base, base_claim, claimed, beneath)
        stepped = self.respelt(stepped, step_claim, reached, under)
        if stepped is None:
            raise self.defect(step.line,
                              'the step does not reach the next instance')
        if base is None:
            raise self.defect(step.line,
                              'the base does not reach the first instance')
        run = self.seq(scope, body, claimed, held, reached, whole,
                  block.base, variable, self.names[name], *ties, base,
                  stepped, lemma)
        # The lemma states the membership apart from the rest of the
        # antecedent, and the scope already holds it, so the two are
        # conjoined back.
        if member not in block.outside:
            raise self.defect(step.line,
                              f'nothing in scope says {member}')
        return whole, self.seq(scope, self.seq(scope, member, 'wa'), whole,
                          self.seq(scope, scope, member, self.seq(scope, 'id'),
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
            raise self.defect(step.line, f'no expansion for {head!r}')
        # The step's own requires lines hold for the whole of it, not only
        # for the helpers that ask `supplied` themselves. A membership asked
        # while turning an equation round in `def:divides` is as much the
        # step's as one asked by the lemma it cites, and the line the page
        # wrote for it is the one to use. Offered as `written` is, which the
        # membership lookup and the one-lemma bridge read and a search does
        # not, so what `settle` searches is no wider.
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

    def said(self, step):
        """Every sentence of a step's claim, as trees.

        `node` above is the last of them, because that is what an expansion
        is about. A line is cited whole, so what it keeps is all of them.
        """
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
        `thm:lowest-terms` gives a numerator and a denominator together.
        """
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
                raise self.defect(step.line,
                                  'an obtain that names neither an item nor '
                                  'a line claiming the existence')
            ex, p_ex = held.term, self.carried(where, facts, lines)
            # Eliminating an existential puts the name it binds into the
            # scope, and the lemma that does it forbids that name in what
            # the scope already says. A `contradiction` supposing an
            # existence is such a scope: the supposition is the scope, and
            # it binds the very name being introduced. So the claim is
            # respelt first, over names nothing else holds.
            standing = {t for t in scope.split()
                        if t in self.sigs and self.sigs[t].kind == '$f'}
            if {self.flabel[v]
                    for v in self.bound_in(self.to_term(ex))} & standing:
                fresh = self.renamed(ex, len(got))
                apart = self.renaming(self.to_term(ex), self.to_term(fresh))
                if apart is None:
                    raise self.defect(step.line,
                                      'the existence this obtains from binds '
                                      'a name the scope already holds')
                p_ex = self.seq(scope, ex, fresh, p_ex,
                           self.seq(self.seq(ex, fresh, 'wb'), scope, apart, 'a1i'),
                           'mpbid')
                ex = fresh
        elif named.group(1).startswith('def:'):
            cites = step.just.text.split(':', 1)[1].strip()
            subject = self.names[instantiation(cites)[0][1]]
            # A fresh name, not the lemma's own: `divides` binds `n`, and a
            # proof that obtains from it twice would introduce one variable
            # for two different numbers.
            # `spare_var` runs out only when a proof has introduced more
            # names than the kernel has letters, which is the tool at its
            # limit rather than a route declining or the text at fault.
            fresh = self.spare_var()
            if declined(fresh):
                raise self.defect(step.line, f'{fresh}')
            lemma, var, kernel, _t, over, left = self.definition(
                named.group(1), subject, var=fresh)
            body = self.term(kernel)
            self.names = saved
            ex = self.seq(body, var, over, 'wrex')
            made = self.unfolding(step, lemma, left, ex, var, over, scope,
                                  facts)
            if declined(made):
                raise self.defect(step.line, f'{lemma} does not unfold '
                                             f'what this obtains from')
            p_ex = self.seq(scope, left, ex, facts[left], made[0], 'mpbid')
        else:
            cites = step.just.text.split(':', 1)[1].strip()
            item = self.items[named.group(1).split(':', 1)[1]]
            for name, value in instantiation(cites):
                self.names[name] = self.term(self.read(value))
            # A name is a variable of the kernel whatever it is spelt with:
            # `x₁` is no set.mm letter, and a spare stands for it as one
            # does for a binder's name.
            for name in got:
                self.names[name] = f'{self.binder_var(name)} cv'
            ex = self.term(self.read(self.claimed_by(item)))
            self.names = saved
            # An item states its existential in its own names, and a binder
            # takes the variable its name is spelled with. The primes proof
            # obtains a p and concludes that there is a p, so the one it
            # obtains is renamed to a variable nothing else is holding.
            ex = self.renamed(ex, len(got))
            p_ex = self.cite_item(step, ex, scope, facts, item, cites)
        # What the line is obtained from is what it rests on; what it
        # introduces is sealed below with the same name, and rests on nothing.
        self.rests_on_named(p_ex, self.named(step, number), step.line,
                            f'step {number}')
        self.does_work(step, number, p_ex)
        p_ex = self.seal(p_ex, number)

        # The existential says which names it introduces and where they run,
        # so the scope is read off it rather than off the text.
        layers, rest = [], self.to_term(ex)
        while len(layers) < len(got):
            body_term, variable, over_term = rest.children
            layers.append((variable.rpn(self.flabel),
                           over_term.rpn(self.flabel)))
            rest = body_term
        body = rest.rpn(self.flabel)

        member = self.seq(*(self.seq(f'{v} cv', s, 'wcel') for v, s in layers))
        if len(layers) > 1:
            member = self.seq(member, 'wa')
        outer, held = self.widen(scope, facts, member, number)
        inner, lifted = self.widen(outer, held, body, number)

        for name, (variable, over_term) in zip(got, layers, strict=True):
            self.names[name] = f'{variable} cv'
            self.sets[name] = over_term
        # Read after the obtained names are bound, so a sentence naming one
        # of them is about the variable the existential introduced.
        lines[number] = Fact(body, lifted[body], self.said(step))

        discharge = 'rexlimdva' if len(layers) == 1 else 'rexlimdvva'
        pushed = [v for v, _s in layers] + [s for _v, s in layers]

        def close(proof, goal):
            return self.seq(scope, ex, goal, p_ex,
                       self.seq(scope, body, goal, *pushed,
                           self.seq(outer, body, goal, proof, 'ex'), discharge),
                       'mpd')

        return inner, lifted, [*closers, close]

    def rebound(self, stated, claimed):
        """Whether two statements differ only in the letters they bind.

        An `obtain` renames what its existential binds, and a name the page
        defines is read with the proof's letters rather than the item's: the
        subsets proof's T binds `o` where `thm:powerset-split-disjoint`'s
        own reading binds `u`. Those are one statement. A letter is bound
        where it stands directly under a constructor other than `cv`; every
        other letter must be the same on both sides.
        """
        pairs, binders = {}, set()

        def alike(one, two):
            if one.variable is not None or two.variable is not None:
                if one.variable is None or two.variable is None:
                    return False
                return pairs.setdefault(one.variable,
                                        two.variable) == two.variable
            if (one.label != two.label
                    or len(one.children) != len(two.children)):
                return False
            if one.label != 'cv':
                binders.update(c.variable for c in one.children
                               if c.variable is not None)
            return all(alike(a, b)
                       for a, b in zip(one.children, two.children,
                                       strict=True))

        return (alike(self.to_term(stated), self.to_term(claimed))
                and len(set(pairs.values())) == len(pairs)
                and all(mine == theirs or mine in binders
                        for mine, theirs in pairs.items()))

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

    def claimed_by(self, item):
        """What an item claims, from wherever its statement lives.

        An item the corpus proves carries no statement in the database, so
        that the statement has one home and cannot drift; the home is the
        `theorem` line of the proof that proves it. One the database states
        outright has it there.
        """
        if item.conclusions:
            return item.conclusions[0][0]
        return self.proofs[item.name].conclusion

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
        # statement claims, and `thm:lowest-terms` is proved here.
        if 'proved-in' in item.fields:
            return self.cite_corpus(step, goal, scope, facts, None, item,
                                    cites)
        labels = targets.clauses(item)
        seed = self.filling(step, item, cites)
        for label in labels:
            found = self.apply_lemma(label, self.to_term(goal), scope, facts,
                                     step, seed=seed)
            if found is not None:
                return found
        assembled = self.from_lemmas(labels, goal, scope, facts, step, seed)
        if assembled is not None:
            return assembled
        if labels:
            # `step.just.head` is the word `obtain` here rather than the item,
            # so the item names itself, and the labels it named say which
            # field to go and look at.
            kind = 'def' if item.kind == 'definition' else 'thm'
            raise self.defect(step.line,
                              f'{kind}:{item.name} targets '
                              f'{", ".join(labels)}, and none of them reaches '
                              f'what step {fmt(step.number)} obtains')
        return self.assume_item(step, goal, scope, facts, item, cites)

    def assume_item(self, step, goal, scope, facts, item, cites=None):
        """An item the database gives no target for, taken as it states itself.

        `thm:lowest-terms` is the case: set.mm has nothing of its shape, as
        `db/items.records` says, so what it claims is assumed under the hypotheses
        it asks for.
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
        # side of it: `thm:abs-difference-lt` says |x − c| < δ exactly when
        # c − δ < x and x < c + δ, and step 17.11 of the intermediate value
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
            if goal not in sides:
                kind = 'def' if item.kind == 'definition' else 'thm'
                raise self.defect(
                    step.line,
                    f'{kind}:{item.name} is taken as stated and states '
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
            # instance a cited line names: `thm:completeness` asks that S be
            # bounded above, and the step cites that b is an upper bound.
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
                    f'{kind}:{item.name} is taken as stated and asks for '
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
        stated about the step's things: `thm:function-value` says `let x ∈
        D`, and the intermediate value proof has no D. A name nothing fixes
        is read as the proof's own letter.
        """
        bound = {}
        for name, value in instantiation(cites or step.just.text):
            bound[name] = self.read(value)
        with self.in_its_names(item):
            ends = [self.read(text) for text, _line in item.conclusions]
            hyps = [self.read(hypothesis_body(kind, text))
                    for kind, text, _label, _line in item.hypotheses]
        variables = set().union(*(names_in(n) for n in [*ends, *hyps]))
        props = binding_context(self.g.notations)[1]
        for end in ends:
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

    def carried(self, cite, facts, lines):
        """A cited line's proof, said where the citing step sits.

        A line proved before a block opened holds inside it too, and the
        scope carries a copy that says so. The line's own proof states it at
        the scope it was made in, which is not where a step inside the block
        can use it.
        """
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
        said = re.match(r'substitute\s+(.*)\s*\([^()]*\)'
                        r'(?:\s+into\s+(\S.*?))?\s*$', text)
        if said is None:
            raise self.defect(step.line,
                              'a substitute that names no equation')
        left, right = self.read(said.group(1)).children
        old, new = self.term(left), self.term(right)
        # Which way the equation faces in the kernel is the lemma's choice,
        # not the text's, so either is accepted and turned if it has to be.
        facing = facts.get(self.seq(old, new, 'wceq'))
        if facing is None:
            held = facts.get(self.seq(new, old, 'wceq'))
            if held is None:
                raise self.defect(step.line,
                                  f'no equation {old} = {new} in scope')
            facing = self.seq(scope, new, old, held, 'eqcomd')
        turned = self.seq(scope, old, new, facing, 'eqcomd')

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

        where = said.group(2).split()[-1]
        into = lines[where]
        if not into.sentences:
            raise self.defect(step.line,
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
                made = self.rewrite(one, was, now, scope, faces)
                if declined(made):
                    continue
                built, proof = made
                if built == term:
                    return self.seq(scope, start, term, known[start], proof,
                               'mpbid')
        raise self.defect(step.line, 'the substitution misses the claim')

    def algebra(self, step, node, term, scope, facts, lines):
        """Decided by `parley/field.py`, then proved by `parley/normal.py`.

        A step that is not an identity of the field is refused rather than
        assumed. One that is gets a proof where `normal.py` can build one:
        both sides are driven to the same canonical term and the step is
        the two of them meeting. What that module does not yet write — a
        quotient, a coefficient past one digit — is taken as stated, which
        is what every `algebra` step was before it existed.
        """
        self.decide_field(step, term, lines)
        found = self.prove_field(step, term, scope, facts, lines)
        if declined(found):
            return self.assume(step, term, scope, facts, 'alg', lines)
        return found

    def prove_field(self, step, term, scope, facts, lines):
        """An `algebra` claim, by whichever of two routes reaches it."""
        goal = self.to_term(term)
        apart = (goal.variable is None and goal.label == 'wn'
                 and len(goal.children) == 1)
        if not apart and (goal.variable is not None or goal.label != 'wceq'
                          or len(goal.children) != 2):
            return Declined('the claim is not an equation')

        self.combining(term)
        # A `requires` line is where a step says its denominator is not
        # zero, so what the normalizer is asked is asked of those as well
        # as of the scope.
        facts = self.supplied(step, scope, facts) if step is not None \
            else facts

        def complex_number(said):
            """What `normal.py` asks of a subterm it does not look inside."""
            return self.membership(said, 'cc', scope, facts)

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
            found = route()
            if not declined(found):
                return found
            declines.append(str(found))
        return Declined('; '.join(declines))

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
        has no such step to check that against.
        """
        if step is None:
            return Declined('a disequality needs the step it cites')
        claim = field.denied(goal, self.flabel)
        left, right = goal.children[0].children
        lhs, rhs = left.rpn(self.flabel), right.rpn(self.flabel)
        whole = self.seq(lhs, rhs, 'cmin', 'co')
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
                gap = self.seq(p, q, 'cmin', 'co')
                given = self.cited_fact(ref, node, scope, facts, lines)
                if declined(given):
                    return given
                apart = work.ap(
                    'subne0d', {'ph': scope, 'A': p, 'B': q},
                    complex_number(p), complex_number(q),
                    work.ap('neqned', {'ph': scope, 'A': p, 'B': q}, given))
                if rescales(cited, claim) == -1:
                    apart = work.ap('negne0d', {'ph': scope, 'A': gap},
                                    complex_number(gap), apart)
                    gap = self.seq(gap, 'cneg')
                alike = self.same_polynomial(work, gap, whole)
                if declined(alike):
                    return alike
                return work.ap(
                    'neneqd', {'ph': scope, 'A': lhs, 'B': rhs},
                    work.ap(
                        'subne0ad', {'ph': scope, 'A': lhs, 'B': rhs},
                        complex_number(lhs), complex_number(rhs),
                        work.ap('eqnetrrd',
                                {'ph': scope, 'A': gap, 'B': whole,
                                 'C': 'cc0'},
                                alike, apart)))
        return Declined('no cited disequality is the claim rescaled')

    def crossed_from_cited(self, step, left, right, scope, facts, lines,
                           work):
        """A claim the cited equation already is, once its division goes.

        sqrt2-irrational concludes `m^2 = 2 j^2` from `( m / j ) ^ 2 = 2`.
        Those are the same equation: the second divides where the first
        has multiplied out, and `divmuleq` is the step between them.
        """
        want = field.equation(self.to_term(self.seq(left, right, 'wceq')),
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
            given = self.cited_fact(ref, cited, scope, facts, lines)
            if declined(given):
                continue
            found = self.cleared(work, cited, left, right, given)
            if not declined(found):
                return found
        return Declined('no cited equation is the claim divided')

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
                      'ps': self.seq(self.seq(a, b, 'cdiv', 'co'),
                                self.seq(c, d, 'cdiv', 'co'), 'wceq'),
                      'ch': self.seq(self.seq(a, d, 'cmul', 'co'),
                                self.seq(c, b, 'cmul', 'co'), 'wceq')},
            work.ap('3eqtr3d', {'ph': work.under, 'A': was[0], 'B': was[1],
                                'C': self.seq(a, b, 'cdiv', 'co'),
                                'D': self.seq(c, d, 'cdiv', 'co')},
                    given, first, second),
            work.ap('syl2anc',
                    {'ph': work.under,
                     'ps': seq(seq(a, 'cc', 'wcel'), seq(c, 'cc', 'wcel'),
                               'wa'),
                     'ch': seq(seq(seq(b, 'cc', 'wcel'),
                                   seq(b, 'cc0', 'wne'), 'wa'),
                               self.seq(self.seq(d, 'cc', 'wcel'),
                                   self.seq(d, 'cc0', 'wne'), 'wa'), 'wa'),
                     'th': self.seq(self.seq(self.seq(a, b, 'cdiv', 'co'),
                                   self.seq(c, d, 'cdiv', 'co'), 'wceq'),
                               self.seq(self.seq(a, d, 'cmul', 'co'),
                                   self.seq(c, b, 'cmul', 'co'), 'wceq'), 'wb')},
                    work.ap('jca', {'ph': work.under,
                                    'ps': self.seq(a, 'cc', 'wcel'),
                                    'ch': self.seq(c, 'cc', 'wcel')},
                            work.run_cc(over), work.run_cc(below)),
                    work.ap('jca', {'ph': work.under,
                                    'ps': self.seq(self.seq(b, 'cc', 'wcel'),
                                              self.seq(b, 'cc0', 'wne'), 'wa'),
                                    'ch': self.seq(self.seq(d, 'cc', 'wcel'),
                                              self.seq(d, 'cc0', 'wne'), 'wa')},
                            work.pair_of(under), work.pair_of(beneath)),
                    work.ap('divmuleq', {'A': a, 'B': c, 'C': b, 'D': d})))
        sides = [self.same_polynomial(work, left, self.seq(a, d, 'cmul', 'co')),
                 self.same_polynomial(work, right, self.seq(c, b, 'cmul', 'co'))]
        for one in sides:
            if declined(one):
                return one
        return work.ap(
            '3eqtr4d', {'ph': work.under, 'A': self.seq(a, d, 'cmul', 'co'),
                        'B': self.seq(c, b, 'cmul', 'co'), 'C': left,
                        'D': right},
            crossed, *sides)

    def not_zero(self, scope, facts):
        """What says a denominator is not zero, asked of the scope.

        The text writes these: `requires 2 =/= 0` and `requires q =/= 0`
        are what a step dividing by either of them carries, so the fact is
        there to be found rather than to be proved again here.
        """
        def apart(said):
            want = self.seq(said, 'cc0', 'wne')
            if want in facts:
                return facts[want]
            denied = self.seq(self.seq(said, 'cc0', 'wceq'), 'wn')
            if denied in facts:
                return self.seq(scope, said, 'cc0', facts[denied], 'neqned')
            found = self.apart_as_written(said, scope, facts)
            if found is not None:
                return found
            # `normal.py` asks this while writing a proof it has already
            # decided, and takes what it is given. A decline handed back
            # there reaches the step as the method not covering it, which
            # is not what a missing `requires` line means.
            settled = self.settle(self.to_term(want), scope, facts)
            if declined(settled):
                raise self.defect(
                    self.at, f'nothing says {self.render(want)}, which this '
                             f'step needs to divide by it')
            return settled
        return apart

    def apart_as_written(self, said, scope, facts):
        """The same fact about the same denominator, spelt as the text spells it.

        A step writes `1 − a ≠ 0` and the normalizer asks about the
        polynomial that is, which it writes as −1·a¹ + 1·1. Those are one
        number and the two lookups above compare spellings, so the fact the
        step wrote is there and is missed. What decides is the polynomial,
        and the equation carrying one spelling to the other is the
        normalizer's own: it is what `normalize` returns beside the terms.
        """
        work = normal.Emitter(
            self.sigs, scope,
            lambda term: self.membership(term, 'cc', scope, facts))
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
                given = self.seq(scope, subject.rpn(self.flabel), 'cc0', proof,
                            'neqned')
            else:
                subject, zero = node.children
                given = proof
            was = subject.rpn(self.flabel)
            if zero.rpn(self.flabel) != 'cc0' or was == said:
                continue
            made = work.normalize(subject, self.flabel)
            if declined(made):
                continue
            items, same = made
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
        for the case above to answer.
        """
        first_items, first_under, first = work.normalize_quotient(
            self.to_term(left), self.flabel)
        second_items, second_under, second = work.normalize_quotient(
            self.to_term(right), self.flabel)
        if first_under is None and second_under is None:
            if work.spell_run(first_items) != work.spell_run(second_items):
                return Declined('the two are not one polynomial')
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
        crossed = self.same_polynomial(work, self.seq(a, d, 'cmul', 'co'),
                                       self.seq(c, b, 'cmul', 'co'))
        return work.ap(
            'eqtr4d', {'ph': work.under, 'A': left,
                       'B': self.seq(a, b, 'cdiv', 'co'), 'C': right},
            first,
            work.ap('eqtrd', {'ph': work.under, 'A': right,
                              'B': self.seq(c, d, 'cdiv', 'co'),
                              'C': self.seq(a, b, 'cdiv', 'co')},
                    second,
                    work.ap('mpbird',
                            {'ph': work.under,
                             'ps': self.seq(self.seq(c, d, 'cdiv', 'co'),
                                       self.seq(a, b, 'cdiv', 'co'), 'wceq'),
                             'ch': self.seq(self.seq(c, b, 'cmul', 'co'),
                                       self.seq(a, d, 'cmul', 'co'), 'wceq')},
                            work.ap('eqcomd',
                                    {'ph': work.under,
                                     'A': self.seq(a, d, 'cmul', 'co'),
                                     'B': self.seq(c, b, 'cmul', 'co')}, crossed),
                            work.ap('syl2anc',
                                    {'ph': work.under,
                                     'ps': self.seq(self.seq(c, 'cc', 'wcel'),
                                               self.seq(a, 'cc', 'wcel'), 'wa'),
                                     'ch': self.seq(self.seq(self.seq(d, 'cc', 'wcel'),
                                                   self.seq(d, 'cc0', 'wne'),
                                                   'wa'),
                                               self.seq(self.seq(b, 'cc', 'wcel'),
                                                   self.seq(b, 'cc0', 'wne'),
                                                   'wa'), 'wa'),
                                     'th': seq(seq(seq(c, d, 'cdiv', 'co'),
                                                   seq(a, b, 'cdiv', 'co'),
                                                   'wceq'),
                                               seq(seq(c, b, 'cmul', 'co'),
                                                   seq(a, d, 'cmul', 'co'),
                                                   'wceq'), 'wb')},
                                    work.ap('jca',
                                            {'ph': work.under,
                                             'ps': self.seq(c, 'cc', 'wcel'),
                                             'ch': self.seq(a, 'cc', 'wcel')},
                                            work.run_cc(below),
                                            work.run_cc(over)),
                                    work.ap('jca',
                                            {'ph': work.under,
                                             'ps': self.seq(self.seq(d, 'cc', 'wcel'),
                                                       self.seq(d, 'cc0', 'wne'),
                                                       'wa'),
                                             'ch': self.seq(self.seq(b, 'cc', 'wcel'),
                                                       self.seq(b, 'cc0', 'wne'),
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
        claim's own difference, which is the normalizer's question.
        """
        want = field.equation(self.to_term(self.seq(left, right, 'wceq')),
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
            return Declined('the step cites no equation')

        def in_cc(said):
            """( scope -> said e. CC ), for a term of the step's own depth.

            The claim's sides are as deep as the step wrote them — Bezout's
            is a sum of two products of a difference of a product — and each
            level is a closure lemma with the atoms at the bottom reached
            through `recn`. Five is not enough for that and is the depth a
            side condition wants, so this asks for its own.

            Built by `part` first, which is that walk done by table with the
            atoms taken from the step's own lines. Searched for, `zcn` stands
            before `mulcl`, and the product came from the hypotheses through
            ℤ while the lines the step wrote for its atoms went unused.
            """
            found = self.part(said, 'cc', scope, facts)
            if not declined(found):
                return found
            return self.settle(self.to_term(self.seq(said, 'cc', 'wcel')), scope,
                               facts, depth=12)

        atoms = {a for p in [*given, want] for m in p.terms for a, _ in m}
        how = field.follows(given, want, atoms)
        if not how:
            return Declined('no sum of the cited equations is the '
                                   'claim')
        self.combining(self.seq(left, right, 'wceq'),
                       *(where[which][1].rpn(self.flabel)
                         for which, _shape, _scale in how))
        pieces = []
        for which, shape, scale in how:
            ref, node = where[which]
            a, b = (c.rpn(self.flabel) for c in node.children)
            gap = self.seq(a, b, 'cmin', 'co')
            times = multiplier(shape, scale)
            if times is None:
                return Declined('a multiplier with no spelling')
            parts = [self.cited_fact(ref, node, scope, facts, lines),
                     in_cc(a), in_cc(b)]
            for one in parts:
                if declined(one):
                    return one
            given, a_cc, b_cc = parts
            vanishes = work.ap(
                'mpbird', {'ph': scope, 'ps': self.seq(gap, 'cc0', 'wceq'),
                           'ch': self.seq(a, b, 'wceq')},
                given,
                work.ap('subeq0ad', {'ph': scope, 'A': a, 'B': b},
                        a_cc, b_cc))
            piece = self.seq(times, gap, 'cmul', 'co')
            pieces.append((piece, work.ap(
                'eqtrd', {'ph': scope, 'A': piece,
                          'B': self.seq(times, 'cc0', 'cmul', 'co'), 'C': 'cc0'},
                work.ap('oveq2d', {'ph': scope, 'A': gap, 'B': 'cc0',
                                   'C': times, 'F': 'cmul'}, vanishes),
                work.ap('mul01d', {'ph': scope, 'A': times},
                        work.atom(times)))))
        total, sums = pieces[0]
        for piece, proof in pieces[1:]:
            joined = self.seq(total, piece, 'caddc', 'co')
            sums = work.ap(
                'eqtrd', {'ph': scope, 'A': joined,
                          'B': self.seq('cc0', 'cc0', 'caddc', 'co'), 'C': 'cc0'},
                work.ap('oveq12d',
                        {'ph': scope, 'A': total, 'B': 'cc0', 'C': piece,
                         'D': 'cc0', 'F': 'caddc'}, sums, proof),
                work.a1i(self.seq(self.seq('cc0', 'cc0', 'caddc', 'co'), 'cc0',
                             'wceq'), '00id'))
            total = joined
        whole = self.seq(left, right, 'cmin', 'co')
        ends = [self.same_polynomial(work, total, whole),
                in_cc(left), in_cc(right)]
        for one in ends:
            if declined(one):
                return one
        alike, left_cc, right_cc = ends
        return work.ap(
            'mpbid', {'ph': scope, 'ps': self.seq(whole, 'cc0', 'wceq'),
                      'ch': self.seq(left, right, 'wceq')},
            work.ap('eqtr3d',
                    {'ph': scope, 'A': total, 'B': whole, 'C': 'cc0'},
                    alike, sums),
            work.ap('subeq0ad', {'ph': scope, 'A': left, 'B': right},
                    left_cc, right_cc))

    def scaled_from_cited(self, step, left, right, scope, facts, lines, work):
        """A claim a cited equation is a whole multiple of.

        sqrt2-irrational concludes `j^2 = 2 p^2` from `2 j^2 = 4 p^2`: the
        equation it cites is the claim with both sides doubled. Proving
        each side is that multiple is the polynomial case again, and what
        is left is cancelling the multiplier.
        """
        want = field.equation(self.to_term(self.seq(left, right, 'wceq')),
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
            scaled = [self.seq(field.NUMERAL[times], one, 'cmul', 'co')
                      for one in (left, right)]
            sides = [self.same_polynomial(work, was, now) for was, now
                     in zip([c.rpn(self.flabel) for c in cited.children],
                            scaled, strict=True)]
            if any(declined(one) for one in sides):
                continue
            self.combining(self.seq(left, right, 'wceq'), held.term)
            return self.cancel_multiple(work, times, left, right, scaled,
                                        sides, self.carried(ref, facts,
                                                            lines),
                                        cited, scope, facts)
        return Declined('no cited equation is a multiple of the claim')

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
            'mpbid', {'ph': scope, 'ps': self.seq(scaled[0], scaled[1], 'wceq'),
                      'ch': self.seq(left, right, 'wceq')},
            matched,
            work.ap('syl3anc',
                    {'ph': scope, 'ps': self.seq(left, 'cc', 'wcel'),
                     'ch': self.seq(right, 'cc', 'wcel'),
                     'th': self.seq(self.seq(numeral, 'cc', 'wcel'),
                               self.seq(numeral, 'cc0', 'wne'), 'wa'),
                     'ta': self.seq(self.seq(scaled[0], scaled[1], 'wceq'),
                               self.seq(left, right, 'wceq'), 'wb')},
                    self.membership(left, 'cc', scope, facts),
                    self.membership(right, 'cc', scope, facts),
                    work.ap('jca', {'ph': scope,
                                    'ps': self.seq(numeral, 'cc', 'wcel'),
                                    'ch': self.seq(numeral, 'cc0', 'wne')},
                            work.number(times),
                            work.a1i(self.seq(numeral, 'cc0', 'wne'),
                                     f'{times}ne0')),
                    work.ap('mulcan', {'A': left, 'B': right,
                                       'C': numeral})))

    def decide_field(self, step, term, lines):
        """Refuse an `algebra` step that is not an identity.

        With nothing cited the claim must vanish outright; with equations
        cited it must be a combination of them. That the denominators are
        not zero is not decided here — the text writes those as `requires`
        lines, which is what `METHODS.md` means by them being hypotheses of
        the method.
        """
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
            raise self.defect(step.line,
                              f'{self.render(term)} is not an identity, nor '
                              f'does it follow from what step '
                              f'{fmt(step.number)} cites')

    def decide_apart(self, step, term, lines):
        """Refuse a disequality `algebra` step that is not a cited one rescaled.

        This method is allowed one disequality and no more: the claim holds
        when what it says does not vanish is a nonzero multiple of what a
        cited disequality says does not vanish. Anything else is a fact
        about the field rather than an identity of it — that a² is not zero
        when a is not needs the field to have no zero divisors, and nothing
        here decides that.

        A claim that is neither an equation nor a disequality is left alone,
        as it was before either was decided.
        """
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
        raise self.defect(step.line,
                          f'{self.render(term)} is not a rescaling of any '
                          f'disequality step {fmt(step.number)} cites')

    def arithmetic(self, step, node, term, scope, facts, lines):
        """Closed numerals, worked out and then said. `METHODS.md`.

        A relation between two numerals is said outright; a value is an
        identity of the field with no atoms in it, so it goes where
        identities go rather than wanting a second procedure.
        """
        for how in (lambda: self.prove_numeral(term, scope, facts),
                    lambda: self.prove_field(step, term, scope, facts,
                                             lines)):
            found = how()
            if not declined(found):
                return found
        return self.assume(step, term, scope, facts, 'ari', lines)

    def prove_numeral(self, term, scope, facts):
        """A closed numeral fact, decided by working it out and then said.

        What `arithmetic` takes is closed, so deciding is arithmetic on two
        whole numbers and needs no procedure. Saying it rests on one thing
        set.mm names for every pair — that one number is below another —
        and everything else is that weakened or turned: `ltle` for `at
        most`, `ltne` for `not equal`, `leid` and `eqid` where the two are
        the same number.
        """
        goal = self.to_term(term)
        negated = False
        if goal.variable is None and goal.label == 'wn' \
                and len(goal.children) == 1:
            negated, goal = True, goal.children[0]
        # Belonging to a number system is the other thing a claim with no
        # atom can say, and `METHODS.md` puts every such claim under this
        # method, so a line saying `arithmetic` for `2 e. ZZ` is decided here
        # rather than by whatever `targets.MEMBERSHIP` reaches.
        if not negated and goal.variable is None and goal.label == 'wcel' \
                and len(goal.children) == 2:
            return self.numeral_within(goal, scope, facts)
        sides = order_sides(goal)
        if sides is None:
            return Declined('the claim states no relation')
        first, second = (linear.numeral(one, self.flabel)
                         for one in sides[:2])
        if first is None or second is None \
                or first.denominator != 1 or second.denominator != 1 \
                or not all(0 <= int(n) <= 9 for n in (first, second)):
            return Declined('the two sides are not single digits')
        # Each side must *be* its digit, not merely come to it. What set.mm
        # names is a fact about the digits, so a side that works out to one
        # without being written as one is a computation, and this is not
        # the method that does computations.
        if any(one.rpn(self.flabel) != field.NUMERAL[int(value)]
               for one, value in zip(sides[:2], (first, second),
                                     strict=True)):
            return Declined('a side works out to a digit but is one '
                                   'only after working out')
        a, b, how = int(first), int(second), sides[2]
        work = normal.Emitter(self.sigs, scope,
                              lambda t: self.membership(t, 'cc', scope, facts))
        if negated:
            if how != '=' or a == b:
                return Declined('a denial of what holds')
            return self.numerals_differ(work, a, b)
        if how == '=' and a == b:
            return work.a1i(self.seq(field.NUMERAL[a], field.NUMERAL[b], 'wceq'),
                            work.ap('eqid', {'A': field.NUMERAL[a]}))
        if how == '<' and a < b:
            return self.numeral_below(work, a, b)
        if how == '<=' and a <= b:
            if a == b:
                return work.ap(
                    'syl', {'ph': scope,
                            'ps': self.seq(field.NUMERAL[a], 'cr', 'wcel'),
                            'ch': self.seq(field.NUMERAL[a], field.NUMERAL[a],
                                      'cle', 'wbr')},
                    self.numeral_real(work, a),
                    work.ap('leid', {'A': field.NUMERAL[a]}))
            return work.ap(
                'mpd', {'ph': scope,
                        'ps': self.seq(field.NUMERAL[a], field.NUMERAL[b], 'clt',
                                  'wbr'),
                        'ch': self.seq(field.NUMERAL[a], field.NUMERAL[b], 'cle',
                                  'wbr')},
                self.numeral_below(work, a, b),
                work.ap('syl2anc',
                        {'ph': scope,
                         'ps': self.seq(field.NUMERAL[a], 'cr', 'wcel'),
                         'ch': self.seq(field.NUMERAL[b], 'cr', 'wcel'),
                         'th': self.seq(self.seq(field.NUMERAL[a], field.NUMERAL[b],
                                       'clt', 'wbr'),
                                   self.seq(field.NUMERAL[a], field.NUMERAL[b],
                                       'cle', 'wbr'), 'wi')},
                        self.numeral_real(work, a),
                        self.numeral_real(work, b),
                        work.ap('ltle', {'A': field.NUMERAL[a],
                                         'B': field.NUMERAL[b]})))
        return Declined(f'{a} {how} {b} is not what the numbers do')

    def numeral_within(self, goal, scope, facts):
        """( scope -> d e. S ), for a digit and a system set.mm names it in.

        `ax-1cn` is the one place the library spells such a label otherwise,
        and where it names none the fact is one it does not state: `0 e. NN`
        is false and `2 e. QQ` unwritten. Both decline here, which leaves
        them where a claim this method cannot decide belongs.
        """
        said, system = goal.children
        suffix = SYSTEMS.get(system.label)
        if suffix is None or system.children:
            return Declined('not a number system set.mm names digits in')
        value = linear.numeral(said, self.flabel)
        if value is None or value.denominator != 1 \
                or not 0 <= int(value) <= 9:
            return Declined('what belongs is not a single digit')
        digit = int(value)
        # As in the relation above: the side must *be* its digit. One that
        # only works out to it is a computation, and this is not the method
        # that does computations.
        if said.rpn(self.flabel) != field.NUMERAL[digit]:
            return Declined('a side works out to a digit but is one '
                            'only after working out')
        label = f'{digit}{suffix}'
        if label not in self.sigs:
            label = f'ax-{label}'
        if label not in self.sigs:
            return Declined(f'set.mm does not state {self.render(goal)}')
        work = normal.Emitter(self.sigs, scope,
                              lambda t: self.membership(t, 'cc', scope,
                                                        facts))
        return work.a1i(self.seq(field.NUMERAL[digit], system.label, 'wcel'),
                        label)

    def numeral_real(self, work, value):
        return work.a1i(self.seq(field.NUMERAL[value], 'cr', 'wcel'),
                        f'{value}re')

    def numeral_below(self, work, a, b):
        """( scope -> a < b ), the one thing set.mm names for every pair.

        It names `0 < n` as `npos` rather than `0ltn`, and one is the
        exception to that, so the three spellings are all there is.
        """
        if a != 0:
            label = f'{a}lt{b}'
        else:
            label = '0lt1' if b == 1 else f'{b}pos'
        return work.a1i(self.seq(field.NUMERAL[a], field.NUMERAL[b], 'clt',
                            'wbr'), label)

    def numerals_differ(self, work, a, b):
        """( scope -> -. a = b ), from whichever of the two is below."""
        low, high = (a, b) if a < b else (b, a)
        apart = work.ap(
            'syl', {'ph': work.under,
                    'ps': self.seq(self.seq(field.NUMERAL[low], 'cr', 'wcel'),
                              self.seq(field.NUMERAL[low], field.NUMERAL[high],
                                  'clt', 'wbr'), 'wa'),
                    'ch': self.seq(field.NUMERAL[high], field.NUMERAL[low],
                              'wne')},
            work.ap('jca', {'ph': work.under,
                            'ps': self.seq(field.NUMERAL[low], 'cr', 'wcel'),
                            'ch': self.seq(field.NUMERAL[low],
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
        those rather than this.
        """
        self.decide_order(step, term, lines)
        # The method wants every atom in ℝ, and a `requires` line is where
        # the step writes that. Reading them here is what puts the page's
        # justification in the proof: settled instead, the membership comes
        # from whatever `targets.MEMBERSHIP` reaches, which is the table for
        # what the readable layer does not write.
        known = self.supplied(step, scope, facts) if step is not None \
            else facts
        # Offered to the membership lookup and to nothing else. `settle`
        # searches what it is given, and widening the facts it sees widens
        # that search: handing `prove_order` the whole of `known` put the
        # four steps of `thm:abs-bounds` past ten million `fits` calls,
        # where the same proof takes five seconds.
        # What a requires line made, and nothing else — including where the
        # scope holds the same claim for another reason, which is the case
        # the line was written for: `requires x ∈ ℝ: from H1` beside the
        # hypothesis that says it.
        kept = self.written
        self.written = {k: (scope, v) for k, v in known.items()
                        if any(o.startswith(REQUIRES)
                               for o in getattr(v, 'origin', ()))}
        try:
            found = self.prove_order(step.just.refs, term, scope, facts,
                                     lines)
        finally:
            self.written = kept
        if declined(found):
            return self.assume(step, term, scope, facts, 'ine', lines)
        return found

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
        is not written yet, so those steps stay assumed.
        """
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
            return Declined('the claim is not linear')
        self.combining(term)
        closed = self.by_antisymmetry(goal, scope, facts)
        if closed is not None:
            return closed
        found = linear.certificate([*given, linear.opposite(claim)])
        if not isinstance(found, dict):
            return self.either_way(found, refs, where, given, term, scope,
                                   facts, lines, skip)
        if len(given) not in found:
            # The denied claim went unused, so the cited facts refute each
            # other and the claim holds because nothing does. That is not
            # this method's to emit; a case of a split says so where it
            # supposed the bound that cannot hold.
            return Declined('the cited facts refute each other')
        used = [i for i, k in found.items() if k and i < len(given)]
        self.combining(term, *(where[i][1].rpn(self.flabel) for i in used))
        weight = found[len(given)]
        if claim.how == '=/=':
            return self.stays_apart(used, given, where, claim, scope, facts,
                                    lines)
        if goal.variable is None and goal.label == 'wn':
            return self.negated_order(goal, refs, term, scope, facts, lines,
                                      skip)
        sides = order_sides(goal)
        if sides is None:
            return Declined('the claim states no relation')
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
            return Declined('what is left over is not a constant')
        return self.from_sum([(where[i], given[i], found[i] / weight)
                              for i in used],
                             left, right, how, spare.constant, scope, facts,
                             lines)

    def by_antisymmetry(self, goal, scope, facts):
        """An equation from the two bounds that close on it.

        A number neither greater nor smaller than another is that number,
        and `letri3` is set.mm saying so. The decision procedure reaches it
        by splitting the claim into its two halves, which is not a split
        any cited line offers, so the two bounds are looked for as they
        stand: Bezout's step 20 has d ≤ gcd(a, b) and gcd(a, b) ≤ d, and
        says the two are equal.
        """
        sides = order_sides(goal)
        if sides is None or sides[2] != '=':
            return None
        a, b = (one.rpn(self.flabel) for one in sides[:2])
        up, down = self.seq(a, b, 'cle', 'wbr'), self.seq(b, a, 'cle', 'wbr')
        if up not in facts or down not in facts:
            return None
        work = normal.Emitter(self.sigs, scope,
                              lambda t: self.membership(t, 'cc', scope, facts))

        def real(one):
            return self.membership(one, 'cr', scope, facts)
        both = self.seq(up, down, 'wa')
        return work.ap(
            'mpbird', {'ph': scope, 'ps': goal.rpn(self.flabel), 'ch': both},
            work.ap('jca', {'ph': scope, 'ps': up, 'ch': down},
                    facts[up], facts[down]),
            work.ap('syl2anc',
                    {'ph': scope, 'ps': self.seq(a, 'cr', 'wcel'),
                     'ch': self.seq(b, 'cr', 'wcel'),
                     'th': self.seq(goal.rpn(self.flabel), both, 'wb')},
                    real(a), real(b), work.ap('letri3', {'A': a, 'B': b})))

    def negated_order(self, goal, refs, term, scope, facts, lines, skip):
        """A claim denying a relation, as the relation that holds instead.

        `not ( d ≤ r )` is `r < d`. `linear.fact` has always read it that
        way — `METHODS.md` calls a negation a fact and not a special case —
        and `order_sides` cannot read a denial at all, so such a claim was
        decided and then had nothing to emit. What holds instead is proved
        first, and `ltnle` or `lenlt` turns it round. Those are two of the
        three labels `db/methods.records` names for this method.
        """
        sides = order_sides(goal.children[0])
        if sides is None or sides[2] not in ('<', '<='):
            return Declined('what is denied states no relation')
        a, b = (one.rpn(self.flabel) for one in sides[:2])
        turns, how = (('ltnle', 'clt') if sides[2] == '<='
                      else ('lenlt', 'cle'))
        instead = self.seq(b, a, how, 'wbr')
        held = facts.get(instead)
        if held is None:
            held = self.prove_order(refs, instead, scope, facts, lines, skip)
            if declined(held):
                return held

        def real(one):
            return self.membership(one, 'cr', scope, facts)
        work = normal.Emitter(self.sigs, scope,
                              lambda t: self.membership(t, 'cc', scope, facts))
        return work.ap(
            'mpbid', {'ph': scope, 'ps': instead, 'ch': term}, held,
            work.ap('syl2anc',
                    {'ph': scope, 'ps': self.seq(b, 'cr', 'wcel'),
                     'ch': self.seq(a, 'cr', 'wcel'),
                     'th': self.seq(instead, term, 'wb')},
                    real(b), real(a), work.ap(turns, {'A': b, 'B': a})))

    def either_way(self, found, refs, where, given, term, scope, facts,
                   lines, skip):
        """A claim proved twice, once each side of a cited disequality.

        `a ≠ b` is `a < b or b < a`, so a refutation that uses one has to
        try both, and `linear.certificate` says so by returning no single
        combination. Each side is the same claim at a scope one wider, with
        the side's bound standing as a line of its own, so the method proves
        it the way it proves anything; a side that splits again is another
        of these. `mpjaodan` puts the two back together.
        """
        _tag, which = found[0], found[1]
        if which >= len(given):
            return Declined('what splits is the claim, not a citation')
        ref, said = where[which]
        if said.variable is not None or said.label != 'wn' \
                or said.children[0].label != 'wceq':
            return Declined('what splits is not a denied equation')
        a, b = (c.rpn(self.flabel) for c in said.children[0].children)
        below, above = (self.seq(a, b, 'clt', 'wbr'), self.seq(b, a, 'clt', 'wbr'))

        work = normal.Emitter(self.sigs, scope,
                              lambda t: self.membership(t, 'cc', scope, facts))

        def real(one):
            return self.membership(one, 'cr', scope, facts)

        given = self.cited_fact(ref, said, scope, facts, lines)
        if declined(given):
            return given
        whether = work.ap(
            'mpbid', {'ph': scope, 'ps': self.seq(a, b, 'wne'),
                      'ch': self.seq(below, above, 'wo')},
            work.ap('neqned', {'ph': scope, 'A': a, 'B': b}, given),
            work.ap('syl2anc',
                    {'ph': scope, 'ps': self.seq(a, 'cr', 'wcel'),
                     'ch': self.seq(b, 'cr', 'wcel'),
                     'th': self.seq(self.seq(a, b, 'wne'),
                               self.seq(below, above, 'wo'), 'wb')},
                    real(a), real(b), work.ap('lttri2', {'A': a, 'B': b})))

        frame, sides = len(self.frames), []
        for bound in (below, above):
            inner, lifted = self.widen(scope, facts, bound)
            held = dict(lines)
            held[bound] = Fact(bound, lifted[bound])
            side = self.one_way(bound, term, inner, lifted, held,
                                [*refs, bound],
                                (*skip, said.rpn(self.flabel)))
            if declined(side):
                del self.frames[frame:]
                return side
            sides.append(side)
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
        and `METHODS.md` counts it refuted rather than proved.
        """
        if term in facts:
            return facts[term]
        found = self.prove_order(refs, term, scope, facts, lines, skip)
        if not declined(found):
            return found
        return self.impossible(bound, term, scope, facts)

    def impossible(self, bound, term, scope, facts):
        """The claim, because the bound this scope opened cannot hold.

        `lenlt` is what says so: a ≤ b and b < a deny each other, and the
        step already has the first where the case supposes the second.
        """
        node = self.to_term(bound)
        sides = order_sides(node)
        if sides is None or sides[2] != '<':
            return Declined('the bound states no strict order')
        low, high = (one.rpn(self.flabel) for one in sides[:2])
        denies = self.seq(high, low, 'cle', 'wbr')
        if denies not in facts:
            return Declined('nothing in scope denies the bound')

        def real(one):
            return self.membership(one, 'cr', scope, facts)
        work = normal.Emitter(self.sigs, scope,
                              lambda t: self.membership(t, 'cc', scope, facts))
        return work.ap(
            'pm2.21dd', {'ph': scope, 'ps': bound, 'ch': term},
            facts[bound],
            work.ap('mpbid', {'ph': scope, 'ps': denies,
                              'ch': self.seq(bound, 'wn')},
                    facts[denies],
                    work.ap('syl2anc',
                            {'ph': scope, 'ps': self.seq(high, 'cr', 'wcel'),
                             'ch': self.seq(low, 'cr', 'wcel'),
                             'th': self.seq(denies, self.seq(bound, 'wn'), 'wb')},
                            real(high), real(low),
                            work.ap('lenlt', {'A': high, 'B': low}))))

    def stays_apart(self, used, given, where, claim, scope, facts, lines):
        """Two things the step says are not equal, because one is below.

        The claim is a denial, so the combination that reaches it is the
        denial supposed and contradicted. Where the contradiction is with
        a single strict bound between the very two the claim names, that
        whole argument is `ltne`: something below another is not it.
        """
        if len(used) != 1 or given[used[0]].how != '<':
            return Declined('not one strict bound')
        ref, said = where[used[0]]
        parts = order_sides(said)
        if parts is None or parts[2] != '<':
            return Declined('the cited bound is not stated as one')
        below = [c.rpn(self.flabel) for c in said.children[:2]]
        # The claim must be about the two the bound is about, and no more.
        if claim.side.minus(given[used[0]].side.scaled(-1)).atoms() \
                or claim.side.minus(
                    given[used[0]].side.scaled(-1)).constant:
            return Declined('the claim is not that bound turned')
        work = normal.Emitter(self.sigs, scope,
                              lambda t: self.membership(t, 'cc', scope, facts))

        def real_number(one):
            return self.membership(one, 'cr', scope, facts)

        bound = self.cited_fact(ref, said, scope, facts, lines)
        if declined(bound):
            return bound
        return work.ap(
            'neneqd', {'ph': scope, 'A': below[1], 'B': below[0]},
            work.ap('syl2anc',
                    {'ph': scope, 'ps': self.seq(below[0], 'cr', 'wcel'),
                     'ch': self.seq(below[0], below[1], 'clt', 'wbr'),
                     'th': self.seq(below[1], below[0], 'wne')},
                    real_number(below[0]), bound,
                    work.ap('ltne', {'A': below[0], 'B': below[1]})))

    def from_sum(self, used, left, right, how, spare, scope, facts, lines):
        """The claim as the cited bounds added, and what they leave over.

        Each says a difference is at most zero; added, the two differences
        are the claim's, which is the normalizer's question. `le2add` is
        the addition, and what it lands on is zero plus zero.

        A claim that is strict gets its strictness from the constant the
        bounds leave over, which is a closed numeral fact the step does
        not cite. `METHODS.md` says the method may use one.
        """
        if how == '<':
            if spare != -1 or len(used) != 1:
                return Declined('only one bound short of one is '
                                       'written')
        elif how != '<=' or spare != 0:
            return Declined('only one or two bounds is written')
        if not 1 <= len(used) <= 2:
            return Declined('only one or two bounds is written')

        def real_number(one):
            return self.membership(one, 'cr', scope, facts)

        work = normal.Emitter(self.sigs, scope,
                              lambda t: self.membership(t, 'cc', scope, facts))
        gaps, bounds, real = [], [], []
        for (ref, said), fact, times in used:
            stated = self.cited_fact(ref, said, scope, facts, lines)
            if declined(stated):
                return stated
            one, proof, held = self.at_most_zero(
                work, said, fact, times, stated, real_number)
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
        total = self.seq(gaps[0], gaps[1], 'caddc', 'co')
        zero = work.a1i(self.seq('cc0', 'cr', 'wcel'), '0re')
        added = work.ap(
            'breqtrd', {'ph': scope, 'A': total,
                        'B': self.seq('cc0', 'cc0', 'caddc', 'co'), 'C': 'cc0',
                        'R': 'cle'},
            work.ap('mpd',
                    {'ph': scope,
                     'ps': self.seq(self.seq(gaps[0], 'cc0', 'cle', 'wbr'),
                               self.seq(gaps[1], 'cc0', 'cle', 'wbr'), 'wa'),
                     'ch': self.seq(total, self.seq('cc0', 'cc0', 'caddc', 'co'),
                               'cle', 'wbr')},
                    work.ap('jca', {'ph': scope,
                                    'ps': self.seq(gaps[0], 'cc0', 'cle', 'wbr'),
                                    'ch': self.seq(gaps[1], 'cc0', 'cle', 'wbr')},
                            *bounds),
                    work.ap('syl',
                            {'ph': scope,
                             'ps': self.seq(self.seq(self.seq(gaps[0], 'cr', 'wcel'),
                                           self.seq(gaps[1], 'cr', 'wcel'), 'wa'),
                                       self.seq(self.seq('cc0', 'cr', 'wcel'),
                                           self.seq('cc0', 'cr', 'wcel'), 'wa'),
                                       'wa'),
                             'ch': seq(seq(seq(gaps[0], 'cc0', 'cle', 'wbr'),
                                           seq(gaps[1], 'cc0', 'cle', 'wbr'),
                                           'wa'),
                                       seq(total,
                                           seq('cc0', 'cc0', 'caddc', 'co'),
                                           'cle', 'wbr'), 'wi')},
                            work.ap('jca',
                                    {'ph': scope,
                                     'ps': self.seq(self.seq(gaps[0], 'cr', 'wcel'),
                                               self.seq(gaps[1], 'cr', 'wcel'),
                                               'wa'),
                                     'ch': self.seq(self.seq('cc0', 'cr', 'wcel'),
                                               self.seq('cc0', 'cr', 'wcel'),
                                               'wa')},
                                    work.ap('jca',
                                            {'ph': scope,
                                             'ps': self.seq(gaps[0], 'cr', 'wcel'),
                                             'ch': self.seq(gaps[1], 'cr',
                                                       'wcel')}, *real),
                                    work.ap('jca',
                                            {'ph': scope,
                                             'ps': self.seq('cc0', 'cr', 'wcel'),
                                             'ch': self.seq('cc0', 'cr', 'wcel')},
                                            zero, zero)),
                            work.ap('le2add', {'A': gaps[0], 'B': gaps[1],
                                               'C': 'cc0', 'D': 'cc0'}))),
            work.a1i(self.seq(self.seq('cc0', 'cc0', 'caddc', 'co'), 'cc0', 'wceq'),
                     '00id'))
        return self.bound_reaches(work, total, added, left, right,
                                  real_number)

    def short_of_one(self, work, gap, bound, gap_real, left, right,
                     real_number):
        """A bound and a minus one, added, to reach a strict claim.

        `leltadd` is the addition that keeps the strictness, and `suble0`
        has no strict twin, so the claim comes back through `ltsubadd`
        with nothing on the right and `addlid` to tidy it.
        """
        scope = work.under
        minus, span = self.seq('c1', 'cneg'), self.seq(left, right, 'cmin', 'co')
        total = self.seq(gap, minus, 'caddc', 'co')
        alike = self.same_polynomial(work, span, total)
        if declined(alike):
            return alike
        zero = work.a1i(self.seq('cc0', 'cr', 'wcel'), '0re')
        pair = seq(seq(gap, 'cr', 'wcel'), seq(minus, 'cr', 'wcel'), 'wa')
        added = work.ap(
            'breqtrd', {'ph': scope, 'A': total,
                        'B': self.seq('cc0', 'cc0', 'caddc', 'co'), 'C': 'cc0',
                        'R': 'clt'},
            work.ap('mpd',
                    {'ph': scope,
                     'ps': self.seq(self.seq(gap, 'cc0', 'cle', 'wbr'),
                               self.seq(minus, 'cc0', 'clt', 'wbr'), 'wa'),
                     'ch': self.seq(total, self.seq('cc0', 'cc0', 'caddc', 'co'),
                               'clt', 'wbr')},
                    work.ap('jca', {'ph': scope,
                                    'ps': self.seq(gap, 'cc0', 'cle', 'wbr'),
                                    'ch': self.seq(minus, 'cc0', 'clt', 'wbr')},
                            bound,
                            work.a1i(self.seq(minus, 'cc0', 'clt', 'wbr'),
                                     'neg1lt0')),
                    work.ap('syl',
                            {'ph': scope,
                             'ps': self.seq(pair,
                                       self.seq(self.seq('cc0', 'cr', 'wcel'),
                                           self.seq('cc0', 'cr', 'wcel'), 'wa'),
                                       'wa'),
                             'ch': self.seq(self.seq(self.seq(gap, 'cc0', 'cle', 'wbr'),
                                           self.seq(minus, 'cc0', 'clt', 'wbr'),
                                           'wa'),
                                       self.seq(total,
                                           self.seq('cc0', 'cc0', 'caddc', 'co'),
                                           'clt', 'wbr'), 'wi')},
                            work.ap('jca',
                                    {'ph': scope, 'ps': pair,
                                     'ch': self.seq(self.seq('cc0', 'cr', 'wcel'),
                                               self.seq('cc0', 'cr', 'wcel'),
                                               'wa')},
                                    work.ap('jca',
                                            {'ph': scope,
                                             'ps': self.seq(gap, 'cr', 'wcel'),
                                             'ch': self.seq(minus, 'cr', 'wcel')},
                                            gap_real,
                                            self.real_numeral(
                                                work, Fraction(-1))),
                                    work.ap('jca',
                                            {'ph': scope,
                                             'ps': self.seq('cc0', 'cr', 'wcel'),
                                             'ch': self.seq('cc0', 'cr', 'wcel')},
                                            zero, zero)),
                            work.ap('leltadd', {'A': gap, 'B': minus,
                                                'C': 'cc0', 'D': 'cc0'}))),
            work.a1i(self.seq(self.seq('cc0', 'cc0', 'caddc', 'co'), 'cc0', 'wceq'),
                     '00id'))
        return work.ap(
            'breqtrd', {'ph': scope, 'A': left,
                        'B': self.seq('cc0', right, 'caddc', 'co'), 'C': right,
                        'R': 'clt'},
            work.ap('mpbid',
                    {'ph': scope, 'ps': self.seq(span, 'cc0', 'clt', 'wbr'),
                     'ch': self.seq(left, self.seq('cc0', right, 'caddc', 'co'),
                               'clt', 'wbr')},
                    work.ap('eqbrtrd', {'ph': scope, 'A': span, 'B': total,
                                        'C': 'cc0', 'R': 'clt'},
                            alike, added),
                    work.ap('syl3anc',
                            {'ph': scope, 'ps': self.seq(left, 'cr', 'wcel'),
                             'ch': self.seq(right, 'cr', 'wcel'),
                             'th': self.seq('cc0', 'cr', 'wcel'),
                             'ta': self.seq(self.seq(span, 'cc0', 'clt', 'wbr'),
                                       self.seq(left,
                                           self.seq('cc0', right, 'caddc', 'co'),
                                           'clt', 'wbr'), 'wb')},
                            real_number(left), real_number(right), zero,
                            work.ap('ltsubadd', {'A': left, 'B': right,
                                                 'C': 'cc0'}))),
            work.ap('syl', {'ph': scope, 'ps': self.seq(right, 'cc', 'wcel'),
                            'ch': self.seq(self.seq('cc0', right, 'caddc', 'co'),
                                      right, 'wceq')},
                    work.ap('recnd', {'ph': scope, 'A': right},
                            real_number(right)),
                    work.ap('addlid', {'A': right})))

    def bound_reaches(self, work, total, added, left, right, real_number):
        """A term at most zero, said of the claim's two sides.

        The normalizer says the term is the claim's difference, and
        `suble0` says a difference at most zero is `<_` between them.
        """
        scope, span = work.under, self.seq(left, right, 'cmin', 'co')
        alike = self.same_polynomial(work, span, total)
        if declined(alike):
            return alike
        return work.ap(
            'mpbid', {'ph': scope, 'ps': self.seq(span, 'cc0', 'cle', 'wbr'),
                      'ch': self.seq(left, right, 'cle', 'wbr')},
            work.ap('eqbrtrd', {'ph': scope, 'A': span, 'B': total,
                                'C': 'cc0', 'R': 'cle'},
                    alike, added),
            work.ap('syl2anc',
                    {'ph': scope, 'ps': self.seq(left, 'cr', 'wcel'),
                     'ch': self.seq(right, 'cr', 'wcel'),
                     'th': self.seq(self.seq(span, 'cc0', 'cle', 'wbr'),
                               self.seq(left, right, 'cle', 'wbr'), 'wb')},
                    real_number(left), real_number(right),
                    work.ap('suble0', {'A': left, 'B': right})))

    def at_most_zero(self, work, said, fact, times, given, real_number):
        """One cited fact, scaled, as a term that is at most zero.

        Everything a sum takes is brought to that one shape first, so the
        addition has one case rather than one per relation. An equation is
        at most zero because it is zero exactly; an inequality already is,
        and scaling it by something positive leaves it so.
        """
        scope = work.under
        if said.variable is None and said.label == 'wn' \
                and len(said.children) == 1:
            said, given = self.unnegated(work, said.children[0], given,
                                         real_number)
        parts = order_sides(said)
        if parts is None:
            return Declined('a cited fact states no relation')
        was = [c.rpn(self.flabel) for c in said.children[:2]]
        gap = self.seq(was[0], was[1], 'cmin', 'co')
        real = work.ap('syl2anc',
                       {'ph': scope, 'ps': self.seq(was[0], 'cr', 'wcel'),
                        'ch': self.seq(was[1], 'cr', 'wcel'),
                        'th': self.seq(gap, 'cr', 'wcel')},
                       real_number(was[0]), real_number(was[1]),
                       work.ap('resubcl', {'A': was[0], 'B': was[1]}))
        numeral = field.spell_coefficient(times)
        if numeral is None:
            return Declined(f'{times} is past one digit')
        scaled = self.seq(numeral, gap, 'cmul', 'co')
        scaled_real = work.ap(
            'syl2anc', {'ph': scope, 'ps': self.seq(numeral, 'cr', 'wcel'),
                        'ch': self.seq(gap, 'cr', 'wcel'),
                        'th': self.seq(scaled, 'cr', 'wcel')},
            self.real_numeral(work, times), real,
            work.ap('remulcl', {'A': numeral, 'B': gap}))
        if parts[2] == '=':
            vanishes = work.chain(
                work.ap('oveq2d', {'ph': scope, 'A': gap, 'B': 'cc0',
                                   'C': numeral, 'F': 'cmul'},
                        self.difference_zero(work, was, given)),
                work.ap('syl', {'ph': scope,
                                'ps': self.seq(numeral, 'cc', 'wcel'),
                                'ch': self.seq(self.seq(numeral, 'cc0', 'cmul', 'co'),
                                          'cc0', 'wceq')},
                        work.coefficient(times),
                        work.ap('mul01', {'A': numeral})),
                scaled, self.seq(numeral, 'cc0', 'cmul', 'co'), 'cc0')
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
            return Declined(f'a cited {parts[2]} is not written')
        bound = self.difference_le(work, was, given, None, real_number)
        if times == 1:
            return gap, bound, real
        if times <= 0:
            return Declined('a bound may only be scaled upward')
        return scaled, work.ap(
            'breqtrd', {'ph': scope, 'A': scaled,
                        'B': self.seq(numeral, 'cc0', 'cmul', 'co'), 'C': 'cc0',
                        'R': 'cle'},
            work.ap('mpbid',
                    {'ph': scope, 'ps': self.seq(gap, 'cc0', 'cle', 'wbr'),
                     'ch': self.seq(scaled, self.seq(numeral, 'cc0', 'cmul', 'co'),
                               'cle', 'wbr')},
                    bound,
                    work.ap('syl3anc',
                            {'ph': scope, 'ps': self.seq(gap, 'cr', 'wcel'),
                             'ch': self.seq('cc0', 'cr', 'wcel'),
                             'th': self.seq(self.seq(numeral, 'cr', 'wcel'),
                                       self.seq('cc0', numeral, 'clt', 'wbr'),
                                       'wa'),
                             'ta': self.seq(self.seq(gap, 'cc0', 'cle', 'wbr'),
                                       self.seq(scaled,
                                           self.seq(numeral, 'cc0', 'cmul', 'co'),
                                           'cle', 'wbr'), 'wb')},
                            real, work.a1i(self.seq('cc0', 'cr', 'wcel'), '0re'),
                            work.ap('jca',
                                    {'ph': scope,
                                     'ps': self.seq(numeral, 'cr', 'wcel'),
                                     'ch': self.seq('cc0', numeral, 'clt',
                                               'wbr')},
                                    self.real_numeral(work, times),
                                    work.a1i(self.seq('cc0', numeral, 'clt',
                                                 'wbr'),
                                             f'{times.numerator}pos')),
                            work.ap('lemul2', {'A': gap, 'B': 'cc0',
                                               'C': numeral}))),
            work.ap('syl', {'ph': scope, 'ps': self.seq(numeral, 'cc', 'wcel'),
                            'ch': self.seq(self.seq(numeral, 'cc0', 'cmul', 'co'),
                                      'cc0', 'wceq')},
                    work.coefficient(times),
                    work.ap('mul01', {'A': numeral}))), scaled_real

    def unnegated(self, work, inner, given, real_number):
        """A cited fact stated as a denial, said the other way round.

        `prime-above` reaches its bound by supposing the opposite and
        finding no witness, so what it has is `-. A < m` where the method
        wants `m <_ A`. `lenlt` is the one saying those are the same.
        """
        parts = order_sides(inner)
        if parts is None or parts[2] != '<':
            return Declined('only a denied `<` is turned round')
        was = [c.rpn(self.flabel) for c in inner.children[:2]]
        turned = self.to_term(self.seq(was[1], was[0], 'cle', 'wbr'))
        return turned, work.ap(
            'mpbird', {'ph': work.under,
                       'ps': self.seq(was[1], was[0], 'cle', 'wbr'),
                       'ch': self.seq(self.seq(was[0], was[1], 'clt', 'wbr'), 'wn')},
            given,
            work.ap('syl2anc',
                    {'ph': work.under, 'ps': self.seq(was[1], 'cr', 'wcel'),
                     'ch': self.seq(was[0], 'cr', 'wcel'),
                     'th': self.seq(self.seq(was[1], was[0], 'cle', 'wbr'),
                               self.seq(self.seq(was[0], was[1], 'clt', 'wbr'), 'wn'),
                               'wb')},
                    real_number(was[1]), real_number(was[0]),
                    work.ap('lenlt', {'A': was[1], 'B': was[0]})))

    def real_numeral(self, work, times):
        """( scope -> n e. RR ) for a whole multiplier."""
        whole = abs(times.numerator)
        held = work.a1i(self.seq(field.NUMERAL[whole], 'cr', 'wcel'),
                        f'{whole}re')
        if times.numerator >= 0:
            return held
        return work.ap('renegcld', {'ph': work.under,
                                    'A': field.NUMERAL[whole]}, held)

    def cited_fact(self, ref, said, scope, facts, lines):
        """The proof of one fact a cited line states.

        A line may say several things at once — `abs-bounds` concludes a
        pair of bounds — and what the step uses is one of them, so the
        line is taken apart the way `opposing` takes one apart.
        """
        want = said.rpn(self.flabel)
        held = self.carried(ref, facts, lines)
        if lines[ref].term == want:
            return held
        known = dict(facts)
        self.unpack(lines[ref].term, held, scope, known)
        if want not in known:
            return Declined('that line does not reach the fact')
        return known[want]

    def difference_le(self, work, was, given, facts, real_number):
        """( scope -> ( A - B ) <_ 0 ) from a cited A <_ B."""
        gap = self.seq(was[0], was[1], 'cmin', 'co')
        return work.ap(
            'mpbird', {'ph': work.under, 'ps': self.seq(gap, 'cc0', 'cle', 'wbr'),
                       'ch': self.seq(was[0], was[1], 'cle', 'wbr')},
            given,
            work.ap('syl2anc',
                    {'ph': work.under, 'ps': self.seq(was[0], 'cr', 'wcel'),
                     'ch': self.seq(was[1], 'cr', 'wcel'),
                     'th': self.seq(self.seq(gap, 'cc0', 'cle', 'wbr'),
                               self.seq(was[0], was[1], 'cle', 'wbr'), 'wb')},
                    real_number(was[0]), real_number(was[1]),
                    work.ap('suble0', {'A': was[0], 'B': was[1]})))

    def from_equation(self, cited, times, left, right, how, scope, facts,
                      lines):
        """The claim as one cited equation, scaled.

        An equation may be multiplied by anything, which is what lets one
        cited equation carry a claim on its own. A combination that uses
        an inequality needs that inequality scaled and added, and is a
        different proof.
        """
        ref, said = cited
        parts = order_sides(said)
        if parts is None or parts[2] != '=':
            return Declined('the cited fact is not an equation')
        numeral = field.spell_coefficient(times)
        if numeral is None:
            return Declined(f'{times} is past one digit')

        def complex_number(term):
            return self.membership(term, 'cc', scope, facts)

        work = normal.Emitter(self.sigs, scope, complex_number)
        was = [c.rpn(self.flabel) for c in said.children]
        gap = self.seq(was[0], was[1], 'cmin', 'co')
        scaled = self.seq(numeral, gap, 'cmul', 'co')
        span = self.seq(left, right, 'cmin', 'co')
        def real_number(one):
            return self.membership(one, 'cr', scope, facts)

        if parts[2] == '=':
            # The cited equation says its difference is zero; scaled, that
            # is the claim's difference, and the normalizer is what says so.
            alike = self.same_polynomial(work, span, scaled)
            stated = self.cited_fact(ref, said, scope, facts, lines)
            for one in (alike, stated):
                if declined(one):
                    return one
            reached = work.chain(
                alike,
                work.chain(
                    work.ap('oveq2d', {'ph': scope, 'A': gap, 'B': 'cc0',
                                       'C': numeral, 'F': 'cmul'},
                            self.difference_zero(work, was, stated)),
                    work.ap('syl',
                            {'ph': scope, 'ps': self.seq(numeral, 'cc', 'wcel'),
                             'ch': self.seq(self.seq(numeral, 'cc0', 'cmul', 'co'),
                                       'cc0', 'wceq')},
                            work.coefficient(times),
                            work.ap('mul01', {'A': numeral})),
                    scaled, self.seq(numeral, 'cc0', 'cmul', 'co'), 'cc0'),
                span, scaled, 'cc0')
            if how == '=':
                return work.ap(
                    'mpbid', {'ph': scope, 'ps': self.seq(span, 'cc0', 'wceq'),
                              'ch': self.seq(left, right, 'wceq')},
                    reached,
                    work.ap('syl2anc',
                            {'ph': scope, 'ps': self.seq(left, 'cc', 'wcel'),
                             'ch': self.seq(right, 'cc', 'wcel'),
                             'th': self.seq(self.seq(span, 'cc0', 'wceq'),
                                       self.seq(left, right, 'wceq'), 'wb')},
                            complex_number(left), complex_number(right),
                            work.ap('subeq0', {'A': left, 'B': right})))
            if how != '<=':
                return Declined(f'a {how} conclusion is not written')
            # A difference that is zero is at most zero.
            at_most = work.ap(
                'eqled', {'ph': scope, 'A': span, 'B': 'cc0'},
                work.ap('syl2anc',
                        {'ph': scope, 'ps': self.seq(left, 'cr', 'wcel'),
                         'ch': self.seq(right, 'cr', 'wcel'),
                         'th': self.seq(span, 'cr', 'wcel')},
                        real_number(left), real_number(right),
                        work.ap('resubcl', {'A': left, 'B': right})),
                reached)
        else:
            return Declined(f'a {how} conclusion is not written')
        # A difference at most zero is what `<_` says of the two sides.
        return work.ap(
            'mpbid', {'ph': scope, 'ps': self.seq(span, 'cc0', 'cle', 'wbr'),
                      'ch': self.seq(left, right, 'cle', 'wbr')},
            at_most,
            work.ap('syl2anc',
                    {'ph': scope, 'ps': self.seq(left, 'cr', 'wcel'),
                     'ch': self.seq(right, 'cr', 'wcel'),
                     'th': self.seq(self.seq(span, 'cc0', 'cle', 'wbr'),
                               self.seq(left, right, 'cle', 'wbr'), 'wb')},
                    real_number(left), real_number(right),
                    work.ap('suble0', {'A': left, 'B': right})))

    def difference_zero(self, work, was, given):
        """( scope -> ( A - B ) = 0 ) from a cited A = B."""
        scope = work.under
        return work.ap(
            'mpbird', {'ph': scope, 'ps': self.seq(self.seq(was[0], was[1], 'cmin',
                                                  'co'), 'cc0', 'wceq'),
                       'ch': self.seq(was[0], was[1], 'wceq')},
            given,
            work.ap('syl2anc',
                    {'ph': scope, 'ps': self.seq(was[0], 'cc', 'wcel'),
                     'ch': self.seq(was[1], 'cc', 'wcel'),
                     'th': seq(seq(seq(was[0], was[1], 'cmin', 'co'), 'cc0',
                                   'wceq'), seq(was[0], was[1], 'wceq'),
                               'wb')},
                    work.atom(was[0]), work.atom(was[1]),
                    work.ap('subeq0', {'A': was[0], 'B': was[1]})))

    def decide_order(self, step, term, lines):
        """Refuse an `inequalities` step that does not follow from its lines.

        A cited line of several sentences supplies each sentence that is a
        linear fact and is ignored for the rest, so citing a line that also
        states a membership is not an error.
        """
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
            raise self.defect(step.line,
                              f'{self.render(term)} does not follow from what '
                              f'step {fmt(step.number)} cites')

    def equivalent(self, step, node, term, scope, facts, lines):
        """A definition whose right side is not an existence claim.

        `def:irrational` says x is irrational exactly when x is real and not
        rational, and the step cites the two lines that say each. The lemma
        gives the biconditional and the lines give its right side, so the
        definition is read the way the text reads it: right to left.
        """
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
        # of the intermediate value proof writes `a ≤ b` for `def:interval`,
        # and the scope would build it from a < b behind the line's back.
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

        `def:set-builder` says that belonging to {t ∈ X : P(t)} is belonging
        to X and having the property, and Cantor's step 3.1.3.1 wants the
        second of those from a line that says the first. So the definition
        is read left to right and what it gives is taken apart.
        """
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
                        else f'{item.name} targets nothing')

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
        elaborates to the conjunction of the six equations `def:congruent`
        lists, so a step reading one of them off names the definition but
        asks for nothing the file does not have: the claim is a conjunct,
        and `unpack` reaches it.
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
        return self.assume(step, term, scope, facts, 'def', lines)

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

        `def:S` says what S(1) is and what S(n + 1) is, and set.mm proves each
        separately. The clause is chosen by which lemma's conclusion is what
        the step claims, so the text never says which.

        A clause that declines is a clause that is not this `then` group,
        and the next one is asked. What it is not is the elaborator's own
        limit: the database named these lemmas, so a step none of them
        reaches is a step claiming what the definition does not say, and
        that is a defect rather than a decline.
        """
        item = self.items[step.just.head.split(':', 1)[1]]
        found = self.by_clause(targets.split_entries(item.fields['target']),
                               term, scope, facts, step,
                               self.filling(step, item))
        if found is None:
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
            return None
        if seed is None or (reads.names() - set(seed)
                            - set(self.bound_in(reads))):
            return None                # nothing fixes the lemma's variables
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
        if strong is None:
            return None
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
        if made is None:
            return None
        want = goal.rpn(self.flabel)
        discharge = 'rexlimdva' if len(layers) == 1 else 'rexlimdvva'
        pushed = [v for v, _s in layers] + [s for _v, s in layers]
        return self.seq(scope, ground.rpn(self.flabel), want, strong,
                   self.seq(scope, body, want, *pushed,
                       self.seq(outer, body, want, made, 'ex'), discharge),
                   'mpd')

    def from_lemmas(self, labels, goal, scope, facts, step, seed):
        """An existence claim its item's lemmas together give.

        `thm:lowest-terms` says a rational is some p over some q with
        nothing above 1 dividing both. set.mm says that of the numerator
        and denominator it names for a rational, in three theorems and no
        existential at all: what they are is `qnumdencl`, that the rational
        is their quotient is `qeqnumdivden`, and that they are coprime is
        `qnumdencoprm`.

        So each is proved at what the `with` target says it is about, and
        the claim introduced at the terms they turn out to be about. The
        lemmas are the ones the database names and the witnesses are read
        off them, which is what keeps this from being a search.
        """
        if not labels or not seed:
            return None
        want = self.to_term(goal)
        if want.label != 'wrex':
            return None
        known = dict(facts)
        for label in labels:
            sig = self.sigs.get(label)
            if sig is None:
                return None
            reads = self.syntax.statement(sig)
            while reads.label == 'wi':
                reads = reads.children[1]
            if reads.names() - set(seed):
                return None      # the target does not say what it is about
            said = reads.substitute(seed).rpn(self.flabel)
            proof = self.apply_lemma(label, self.to_term(said), scope, facts,
                                     step, crossing=False, seed=seed)
            if proof is None:
                return None
            known[said] = proof
            self.unpack(said, proof, scope, known)
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
            return None
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
                    return None
            witness = stood[name]
            instance = self.prove_essential(
                self.to_term(self.seq(self.seq(f'{var} cv', witness, 'wceq'),
                                 self.seq(ph, ps, 'wb'), 'wi')), scope, facts)
            member = self.seq(witness, over, 'wcel')
            stands = self.settle(self.to_term(member), scope, facts)
            if declined(stands):
                return None
            proof = self.seq(scope, self.seq(member, ps, 'wa'),
                        self.seq(ph, var, over, 'wrex'),
                        self.seq(scope, member, ps, stands, proof, 'jca'),
                        ph, ps, var, witness, over, instance, 'rspcev',
                        'syl')
        return proof

    def bound_in(self, term):
        """The variables an existential's own binders introduce.

        Outermost first, in the order the existential writes them, because a
        caller handing each of them a spare variable hands them out in this
        order and the proof it writes says which. A set here spelt the same
        proof two ways from one run to the next, and the build's report that
        nothing changed is the only evidence a change moved no proof.
        """
        out, rest = [], term
        while rest.label in ('wrex', 'wreu'):
            out.append(rest.children[1].variable)
            rest = rest.children[0]
        return tuple(out)

    def as_generalised(self, label, goal, scope, facts, step, seed):
        """A lemma said of every such name.

        `dvdslegcd` says a common divisor is no greater than the gcd, of
        whatever divisor it is given, and `def:gcd` says it of every e in
        ℕ. The name is fixed, the lemma applied to it, and `ralrimiva`
        gives it back — the same move a `fix` block closes with, over a
        lemma rather than over a block.
        """
        if goal.label != 'wral':
            return None
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
        if proof is None:
            return None
        return self.seq(scope, body.rpn(self.flabel), variable.rpn(self.flabel),
                   over.rpn(self.flabel), proof, 'ralrimiva')

    def as_conjunct(self, label, whole, reads, goal, scope, facts, step, seed):
        """One half of what a lemma concludes.

        `gcddvds` says in one conjunction that a gcd divides both its
        arguments, and `def:gcd` states those as two sentences because a
        reader reads them as two. The half the claim is fixes the lemma,
        and `simpld` or `simprd` takes it.
        """
        if reads.label != 'wa' or len(reads.children) != 2:
            return None
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
            if proof is None:
                continue
            a, b = (one.rpn(self.flabel) for one in said.children)
            return self.seq(scope, a, b, proof, 'simpld' if i == 0 else 'simprd')
        return None

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
            return None
        said = reads.substitute(seed)
        if said.rpn(self.flabel) == goal.rpn(self.flabel):
            return None
        proof = self.apply_lemma(label, said, scope, facts, step,
                                 crossing=False, seed=seed)
        if proof is None:
            return None
        # No bridge means the lemma is not this claim said otherwise. A
        # target may name several lemmas, each giving a part of what the
        # item says, and then none of them is.
        across = self.bridging(said, goal, scope, facts, step)
        if declined(across):
            across = self.by_equation(said, goal, scope, facts, step)
        if across is None or declined(across):
            return None
        return self.seq(scope, said.rpn(self.flabel), goal.rpn(self.flabel), proof,
                   across, 'mpbid')

    def by_equation(self, said, goal, scope, facts, step):
        """A lemma's conclusion carried to the claim by an equation proved.

        `hashun` says the size of a disjoint union is the sum of the two
        sizes; `thm:card-disjoint-union` assumes each size is a number and
        states the claim in those numbers, so what stands between the two
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

        The bridge comes from `targets.MEMBERSHIP` and nowhere else, which
        is the rule that stops an elaborator reaching a claim by whatever it
        can find that fits.
        """
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
                alike = self.settle(self.to_term(self.seq(said, want, 'wb')),
                                    scope, facts)
                if declined(alike):
                    continue
                return self.seq(scope, said, want, found, alike, 'mpbid')
        return None

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
            if got is None or declined(got):
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
                    if through is not None:
                        return through
                    seeded = self.as_seeded(label, reads, goal, scope, facts,
                                            step, seed)
                    if seeded is not None:
                        return seeded
                    part = self.as_conjunct(label, whole, reads, goal, scope,
                                            facts, step, seed)
                    if part is not None:
                        return part
                    every = self.as_generalised(label, goal, scope, facts,
                                                step, seed)
                    if every is not None:
                        return every
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
                # The near side may be the claim said differently, and only
                # a full seed can tell: `hashen` equates two sizes and the
                # step claims one of them, so nothing in the goal matches
                # either side and nothing in it fixes the lemma's classes.
                if crossing:
                    seeded = self.as_seeded(label, reads.children[0], goal,
                                            scope, facts, step, seed)
                    if seeded is not None:
                        return seeded
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
            pieces, parts = [], [slot]
            while parts:
                part = parts.pop(0)
                if part.label in ('wa', 'w3a'):
                    parts[:0] = part.children
                else:
                    pieces.append(part)
            for piece in pieces:
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
            first = proof.text.split()[-1] == label and not carried
            fold = {('wi', True): 'syl', ('wi', False): 'mpd',
                    ('wb', True): 'sylib', ('wb', False): 'mpbid',
                    (TURNED, True): 'sylibr', (TURNED, False): 'mpbird'}
            # `mpbird` names the two sides in the order it states them, and
            # a crossed biconditional states the claim first; every other
            # fold states what is asked first.
            sides = ((rest, asks.rpn(self.flabel))
                     if joins[i] is TURNED and not first
                     else (asks.rpn(self.flabel), rest))
            under = self.settle(asks, where, known)
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

    def scope_origin(self, scope, facts):
        """The page items a scope is the conjunction of."""
        out, todo = set(), [scope]
        while todo:
            one = todo.pop()
            held = getattr(facts.get(one), 'origin', None)
            if held:
                out |= held
                continue
            node = self.to_term(one)
            if node.variable is None and node.label == 'wa' \
                    and len(node.children) == 2:
                todo.extend(c.rpn(self.flabel) for c in node.children)
        return frozenset(out)

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
        if proof is None:
            return Declined(f'{label} proves nothing at its own value')
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
            return self.settle(right, under, wider)
        return self.settle(right, under, {})

    def allowed(self, sig, binding, variables):
        """The innermost scope a lemma's disjointness conditions permit.

        `fsump1` forbids its summation variable in the antecedent, and the
        induction hypothesis is an equation between sums, so it holds that
        variable. The step is written inside that scope and cannot be proved
        there. It is proved one frame out and carried back in.
        """
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
        return Declined('no scope satisfies the lemma'), None

    def frames_facts(self, frame, facts):
        """What is known at one frame, which is what was known when it opened."""
        return facts if frame == len(self.frames) - 1 else self.frames[frame][2]

    def carry(self, proof, claim, frame):
        """Bring a proof from an outer frame back to the innermost one."""
        for index in range(frame, len(self.frames) - 1):
            outer, added = self.frames[index][0], self.frames[index + 1][1]
            proof = self.seq(outer, claim, added, proof, 'adantr')
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
        assumption that drops them leaves them unused and unchecked.
        """
        asks = []
        for ref in step.just.refs:
            cited = lines[ref]
            asks.append((cited.term, self.carried(ref, facts, lines)))
        for want, (_t, how, line) in zip(
                [self.read(t) for t, _h, _l in step.requires], step.requires,
                strict=True):
            here = self.term(want)
            if here not in [a for a, _p in asks]:
                # Proved from its reason and checked against it, as
                # `supplied` and `required` prove one, so the step rests on
                # the line and not on whatever the line was proved from.
                made = self.side(want, how, scope, facts, step)
                if not declined(made):
                    made = self.discharged_by(made, step, how, line)
                asks.append((here, made))

        statement = term
        for one, _given in reversed(asks):
            statement = self.seq(one, statement, 'wi')
        proof = self.stated(prefix, '|- ' + self.render(statement))
        if not asks:
            # Nothing to discharge, so the statement is simply taken at the
            # scope the step sits in.
            return self.seq(term, scope, proof, 'a1i')
        # The conditions nest, outermost first, so each is answered in turn
        # and what is left of the statement shrinks by one.
        for i, (one, given) in enumerate(asks):
            rest = term
            for later, _p in reversed(asks[i + 1:]):
                rest = self.seq(later, rest, 'wi')
            proof = self.seq(scope, one, rest, given, proof,
                        'syl' if i == 0 else 'mpd')
        return proof

    def stated(self, prefix, text):
        """Register a statement this file takes rather than proves.

        What a statement asks to be pushed is every variable it mentions, in
        the order the database declares them, which is not the order the
        statement happens to write them in. The same statement asked for
        twice is listed once: two steps may need the same arithmetic.
        """
        if text in self.assumed:
            return self.assumed[text]
        label = self.fresh(prefix)
        self.axioms.append((label, text))
        free = sorted({t for t in text.split() if t in self.flabel},
                      key=lambda v: self.forder[self.flabel[v]])
        self.sigs[label] = Signature(
            label, '$a', text.split(),
            [(self.sigs[self.flabel[v]].statement[0], v) for v in free])
        self.assumed[text] = self.seq(*(self.flabel[v] for v in free), label)
        return self.assumed[text]

    def binder_var(self, name):
        """The setvar a binder's name stands for.

        A name is a letter and set.mm may have declared that letter as a
        class: Cantor quantifies over B, and B there is a class variable.
        So the letter's own label is taken only when it names a setvar, and
        a spare stands in otherwise — the same one every time, since the
        name is one name wherever the proof writes it.
        """
        if name in self.bound_as:
            return self.bound_as[name]
        label = self.flabel.get(name)
        if not (label and self.sigs[label].statement[0] == 'setvar'):
            label = self.spare_var()
        self.bound_as[name] = label
        return label

    def fixed_var(self, name, scope=''):
        """The variable a fixed name takes.

        Its own letter where nothing else is holding it, because the claim
        the block states binds that letter and the two have to agree: the
        `fix` in Cantor introduces the x that `for every x ∈ A` quantifies.
        A spare otherwise, as when a notation already binds the letter, or
        when set.mm declares the letter a class — the subsets proof fixes
        an X, and X there is a class variable.

        Agreement is why the answer is kept where a binder's is: the claim
        reads its quantifier through `binder_var`, and within the block the
        two are one binding.

        Kept, and not read. A name a block fixes is that block's, whatever
        the scope already binds by the same word: the subsets proof assumes
        `for every set X` and then fixes an X, and instantiating that
        assumption at a term about the fixed one would capture it if the
        two were one variable. So what the scope holds is avoided, and
        `close_block` gives the word back when the block ends.

        What the scope does not hold is free to agree, which is why the
        Cantor proof's fixed x is the x its conclusion quantifies.
        """
        own = self.flabel.get(name)
        held = ({t.split()[0] for t in self.names.values()
                 if isinstance(t, str) and t.endswith(' cv')}
                | {t for t in scope.split()
                   if t in self.sigs and self.sigs[t].kind == '$f'})
        if not (own and self.sigs[own].statement[0] == 'setvar'
                and own not in held and own not in self.taken):
            own = self.spare_var()
        self.bound_as[name] = own
        return own

    def spare_var(self):
        """A kernel variable no name in this proof is already standing for.

        The names a proof introduces do not all come from here: the first
        `obtain` takes its variables from the existential the item states, so
        a later step asking for a spare can be handed one of them.

        What a name stands for now is not all of it. A binder's name stands
        for its variable only while its body is read, and `bound_as` is
        what says so for the rest of the proof. Bezout defines S over an m
        before any step writes one; handing that m out again would make one
        variable of two binders, and a lemma eliminating either of them
        forbids the other in what it carries.
        """
        held = ({t.split()[0] for t in self.names.values()
                 if isinstance(t, str) and t.endswith(' cv')}
                | self.reserved | set(self.bound_as.values()))
        while self.spare and self.spare[0] in held:
            self.spare.pop(0)
        if not self.spare:
            return Declined('no variable left to introduce a name with')
        return self.spare.pop(0)

    def fresh(self, prefix):
        """A label for a generated statement nothing else is using.

        `ine1` reads as the first inequality assumed; set.mm reads it as
        `_i =/= 1`, and a file that includes another numbers its own from one
        as well. So the label says which file it belongs to, and is looked
        for rather than taken: the library is large enough that a short name
        is never safely free.
        """
        stem = label_of(self.thm.name, self.sigs, self.thm.path,
                        self.thm.line)
        number = len(self.axioms) + 1
        while f'{stem}.{prefix}{number}' in self.sigs:
            number += 1
        return f'{stem}.{prefix}{number}'

    def supplied(self, step, scope, facts):
        """The facts a step's own `requires` lines put within reach.

        A lemma asks for what it asks for, and the text writes what a reader
        would want written: `resqrtth` wants 0 ≤ 2 and the step says so. The
        lines are proved once and offered alongside what the scope holds.

        A lemma applied where no step is passed has none of these to read,
        and what the scope holds is all there is.

        A line naming an item is that item cited, and citing it asks the
        step for its own `requires` lines again. The one being proved is
        not among what can prove it, so it is held out while it is.
        """
        known = dict(facts)
        for text, how, line in (step.requires if step is not None else ()):
            want = self.read(text)
            term = self.term(want)
            if term in self.supplying:
                continue
            # A claim the scope already holds is taken as it stands only
            # where this line's own reason made that proof. This runs more
            # than once for a step, and what one pass proves is passed on to
            # the next, so that is the common case. Held for any other
            # reason, the proof rests on something the line does not say:
            # `isosceles` holds `A ≠ B` from its hypothesis, and the line
            # asking for it says it comes from line 6. A line resting on the
            # lines it cites is always read from them, which is a lookup.
            given = known
            if term in known and not self.rests_on_lines(how):
                # This line's own proof carries the line as its origin.
                if requirement(line) in getattr(known[term], 'origin', ()):
                    continue
                given = {k: v for k, v in known.items() if k != term}
            self.supplying.add(term)
            try:
                made = self.side(want, how, scope, given, step)
            finally:
                self.supplying.discard(term)
            if not declined(made):
                made = self.discharged_by(made, step, how, line)
            known[term] = made
        return known

    def with_cited(self, step, scope, known):
        """The facts a lemma is answered from, what the step cites first.

        Each line the step cites is taken apart on its own and laid over the
        scope's copies of the same claims. The scope holds one proof per
        claim, and which line put it there is not the step's to choose:
        `thm:from-contradiction` asks for P and not P, the step cites the
        line joining them, and the scope held each from the line before.
        """
        # First in order as well, because a lemma's open antecedent is
        # matched against these in turn and takes the first that fits:
        # `pm2.21` asks for a negation, and the one it wants is the one the
        # step cites, not the first the scope happens to hold.
        cited = {}
        for ref in (step.just.refs if step is not None else ()):
            line = self.lines.get(ref)
            if line is None:
                continue
            parts = {line.term: self.carried(ref, known, self.lines)}
            self.unpack(line.term, parts[line.term], scope, parts)
            cited.update(parts)
        return {**cited,
                **{k: v for k, v in known.items() if k not in cited}}

    def rests_on_lines(self, how):
        """Whether a `requires` line's reason is the lines it cites.

        `from H1` is, and so is a definition the database gives no target
        for, which the notation folds into the line it is unfolded at.
        """
        reason = how.strip().split(',')[0].strip()
        if reason.startswith('from '):
            return True
        kind, _, name = reason.partition(':')
        if kind != 'def' or not name.strip():
            return False
        item = self.items.get(name.split()[0])
        return item is not None and item.kind == 'definition' \
            and not targets.clauses(item)

    def unfolded_at(self, term, scope, facts, refs):
        """What a line a `requires` line names says, taken apart.

        A definition the database gives no target for is one the notation
        folds away, so there is nothing in the library to cite and the
        unfolding is the line itself: `A, B, C form a triangle` is four
        claims conjoined, and a line asking for one of them is asking for a
        conjunct of the line it names. A `from H1` reason asks the same of
        the line it names, with no definition between.
        """
        for ref in refs:
            line = self.lines.get(ref)
            if line is None:
                continue
            held = {line.term: self.carried(ref, facts, self.lines)}
            self.unpack(line.term, held[line.term], scope, held)
            if term in held:
                return held[term]
            # What the line says beyond its recorded term: an obtain records
            # the body it obtained, and `c ∈ ℝ` went into the scope when the
            # name's domain was assumed. Its origin is the line, and that is
            # what makes it the line's to give.
            found = facts.get(term)
            if found is not None and getattr(found, 'origin', None) == {ref}:
                return found
        return Declined('no line this names says it')

    def side(self, want, how, scope, facts, step=None):
        """A proof of what one `requires` line asks for.

        A `requires` line may name the lines it rests on, and a method that
        is not expanded has to say so. `requires q ≠ 0: inequalities, from
        3.1` asks only that a positive number is not zero; an assumption
        that drops the 3.1 asks that the number is not zero, which is more
        than the line says and leaves 3.1 unused.
        """
        # While the line is proved, what it cites is what may be carried
        # without a search.
        citing, self.citing = self.citing, frozenset(citations(how))
        try:
            return self.by_its_reason(want, how, scope, facts, step)
        finally:
            self.citing = citing

    def by_its_reason(self, want, how, scope, facts, step=None):
        """`side`, with what the line cites in hand."""
        term = self.term(want)
        # Read from the lines it cites before the scope is asked, since the
        # scope may hold the same claim for another reason.
        if self.rests_on_lines(how):
            found = self.unfolded_at(term, scope, facts, citations(how))
            if declined(found):
                raise self.defect(self.at,
                                  f'{how.strip()} does not reach '
                                  f'{self.render(term)}, which this line '
                                  f'claims it supplies')
            return found
        if term in facts:
            return facts[term]
        closure = how.strip().split(',')[0].strip()
        # A line naming a method is discharged by the method it names. A
        # closed numeral inequality is what `arithmetic` decides outright,
        # and a declared lemma reaching the same fact reaches it the long
        # way round: 1 < 2 through membership of ℤ≥2 costs five lemmas.
        if closure == 'arithmetic':
            found = self.prove_numeral(term, scope, facts)
            if not declined(found):
                return found
        # A line naming an item is that item cited, the same as a step
        # naming it. `GOALS.md` decision 9 is why this stands before the
        # routes below: the readable text is canonical and the kernel proof
        # is derived from it, so what the line says supplies the fact is
        # what supplies it, and not whatever `targets.MEMBERSHIP` reaches.
        #
        # Only where the item has a target. Citing one without is assuming
        # it, and the lists at the head of each elaborated file are what
        # `GEOMETRY.md` measures the corpus by.
        #
        # The name ends at the first space, because what follows it is the
        # instantiation: `thm:abs-real x := a, from H1` names `abs-real` and
        # not `abs-real x := a`.
        if step is not None and closure.split(':', 1)[0] in ('thm', 'def'):
            item = self.items.get(closure.split(':', 1)[1].split()[0])
            if item is not None and targets.clauses(item):
                return self.cite_item(step, term, scope, facts, item, how)
        if closure == 'arithmetic':
            # A value is the other thing `arithmetic` decides, and a closed
            # one is an identity of the field with no atoms in it, so it
            # goes where identities go rather than wanting a second
            # procedure. `METHODS.md` lists the two as one method, so both
            # halves are tried before anything generic: a line naming the
            # method and reaching it through `settle` instead is the method
            # not being asked rather than the method failing.
            found = self.prove_field(None, term, scope, facts, self.lines)
            if not declined(found):
                return found
        if closure == 'inequalities':
            # A side condition resting on a method is proved the way a step
            # resting on it is, where the method can prove one at all.
            found = self.prove_order(citations(how), term, scope, facts,
                                     self.lines)
            if not declined(found):
                return found
        # Nothing generic stands here. A route that settles the claim from
        # wherever the scope holds it rests the proof on something other than
        # the reason the line gives, and the file still verifies, so nothing
        # would show it. What is left is a method saying at the head of the
        # file that it was not expanded, or an error naming the line.
        if closure in ('arithmetic', 'inequalities', 'algebra'):
            # A side condition resting on a closure method rests on it the
            # same way a step does, and is listed the same way: under what
            # the line cites, and under nothing else.
            asks = [(self.lines[ref].term,
                     self.carried(ref, facts, self.lines))
                    for ref in citations(how) if ref in self.lines]
            statement = term
            for one, _given in reversed(asks):
                statement = self.seq(one, statement, 'wi')
            proof = self.stated(closure[:3], '|- ' + self.render(statement))
            if not asks:
                return self.seq(term, scope, proof, 'a1i')
            for i, (one, given) in enumerate(asks):
                rest = term
                for later, _p in reversed(asks[i + 1:]):
                    rest = self.seq(later, rest, 'wi')
                proof = self.seq(scope, one, rest, given, proof,
                            'syl' if i == 0 else 'mpd')
            return proof
        raise self.defect(self.at,
                          f'{how.strip()} does not reach '
                          f'{self.render(term)}, which this line claims '
                          f'it supplies')

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

        def held(cite, turned):
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
        here, instance = self.rewrite(shape, stands, witness, at,
                                      self.seq(at, 'id'))

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
        if declined(spare):
            raise self.defect(step.line, f'{spare}')
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
        line, by walking the shape the definition states against it.
        """
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
            raise self.defect(step.line, 'no cited line names a witness')
        at = self.seq(f'{var} cv', witness, 'wceq')
        _built, instance = self.rewrite(kernel, f'{var} cv', witness, at,
                                        self.seq(at, 'id'))

        ex = self.seq(body, var, over, 'wrex')
        member = self.seq(witness, over, 'wcel')
        p_member = self.required(step, member, over, scope, facts)
        # The cited line faces the way the text writes the definition, and
        # the existential faces the way the lemma writes it.
        # A line proved before a block opened holds inside it too, and the
        # scope's own copy is what says so where the step sits.
        p_cited = facts.get(cited.term, cited.proof)
        if cited.term != here:
            was = self.to_term(cited.term)
            p_cited = self.seq(scope, *(c.rpn(self.flabel) for c in was.children),
                          p_cited, 'eqcomd')
        p_ex = self.seq(scope, self.seq(member, here, 'wa'), ex,
                   self.seq(scope, member, here, p_member, p_cited, 'jca'),
                   body, here, var, witness, over, instance, 'rspcev', 'syl')

        made = self.unfolding(step, lemma, term, ex, var, over, scope, facts)
        if declined(made):
            return made
        return self.seq(scope, term, ex, p_ex, made[0], 'mpbird')

    def join(self, step, node, term, scope, facts, lines):
        """Two lines paired, which is one thing inside a contradiction and
        another outside it.

        Inside, it emits nothing: `pm2.65d` closes the block and consumes
        both joined lines itself, so the join only records which pair. Inside
        a case it is `jca`, and the lines are paired by what they claim, since
        the text lists them in the order they were derived and the conclusion
        states them in the theorem's order. `ELABORATION.md` requirement 8.
        """
        self.joined = [lines[ref].term for ref in step.just.refs]
        if self.enclosing is not None \
                and self.enclosing.owner.just.head == 'contradiction':
            return None
        wanted = self.claim_of(' '.join(step.claim))
        held = {lines[ref].term: self.carried(ref, facts, lines)
                for ref in step.just.refs}
        # One line joined is that line restated: a case whose assumption is
        # the block's claim ends on it, as the intermediate value proof's
        # second case does with `join C2`.
        if len(step.just.refs) == 1:
            if wanted not in held:
                raise self.defect(step.line,
                                  'the joined line is not what the step '
                                  'claims')
            return held[wanted]
        left, right = self.to_term(wanted).children
        pair = [left.rpn(self.flabel), right.rpn(self.flabel)]
        if not all(p in held for p in pair):
            raise self.defect(step.line,
                              'the joined lines are not what the step claims')
        return self.seq(scope, *pair, *(held[p] for p in pair), 'jca')

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
            # `thm:lowest-terms` is the case, and `thm:angle-symmetric`.
            return self.assume_item(step, term, scope, facts, item)
        seed = self.filling(step, item)
        found = self.by_clause(labels, term, scope, facts, step, seed)
        if found is None:
            raise self.defect(step.line,
                              f'no clause of {step.just.head} reaches what '
                              f'step {fmt(step.number)} claims')
        return found

    def by_clause(self, labels, term, scope, facts, step, seed):
        """What one clause of an item gives, or what several give together.

        An item may state several things and set.mm prove each separately,
        which is why a target names one lemma per `then` group. A step
        usually claims one of them — `def:sqrt` is cited three times over —
        but it may claim what the item says entire, as Bezout's step 15
        says what a gcd is in four sentences, and then the clauses are
        taken one to a sentence and joined.
        """
        for label in labels:
            found = self.apply_lemma(label, self.to_term(term), scope,
                                     facts, step, seed=seed)
            if declined(found):
                continue          # not this `then` group; ask the next
            if found is not None:
                return found
        node = self.to_term(term)
        if node.label != 'wa':
            return None
        halves = [self.by_clause(labels, one.rpn(self.flabel), scope, facts,
                                 step, seed) for one in node.children]
        if any(one is None for one in halves):
            return None
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
        other = self.proofs[item.name]
        if item.name not in self.cited:
            self.cited.append(item.name)
        saved, kept = dict(self.names), dict(self.sets)
        spare = list(CLASS_NAMES)
        written = dict(instantiation(cites or step.just.text))
        binds = {}
        for kind, htext, _label, _line in other.hypotheses:
            node = self.read(hypothesis_body(kind, htext))
            # `let X be a set` names a class as surely as `let n ∈ ℕ` does;
            # `hypothesis_body` has already turned it into the formula that
            # says so, and the name is in the same place.
            if kind == 'let' and node.notation in ('membership', 'is-a-set'):
                name = node.children[0].text
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
        # `thm:abs-bounds` concludes x ≤ |x| and −x ≤ |x|, and a step that
        # needs only the first says only the first. The theorem gives the
        # whole, read in its own sorts, and the sentence is taken out of it.
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
        pushed = (self.cited_pushes(item.name, binds, mine)
                  or [binds.get(label, label) for label in mine])
        cited = label_of(item.name, self.sigs, self.thm.path, self.thm.line)
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

    def required(self, step, goal, want, scope, facts):
        """The `requires` line that supplies one side condition.

        A lemma can ask for more than the text writes: `divides` wants both
        sides of `d || n` in ZZ, and only the side a reader could doubt is
        written down. What no line supplies is settled from the term.
        """
        written = {self.term(self.read(t)) for t, _h, _l in step.requires}
        # The scope's copy of a claim is taken only where no line of the
        # step writes it: `let x ∈ ℤ` and `requires x ∈ ℤ: from K1` are one
        # claim, and the step names the second.
        if goal in facts and goal not in written:
            return facts[goal]
        # A lemma may ask its side conditions as one conjunction where the
        # text writes a line each: `divides` wants ( M e. ZZ /\ N e. ZZ )
        # and the step says `requires d ∈ ℤ` and `requires c ∈ ℤ`. Asking
        # whether the whole goal is what a line says misses both, so a
        # conjunction the lines do name between them is answered a part at
        # a time. Only then: a conjunction no line touches is left to the
        # route below, which is what proved it before.
        whole = self.to_term(goal)
        if any(one.rpn(self.flabel) in written for one in whole.children):
            joined = self.conjoined(
                whole, scope,
                lambda one: self.required(step, one.rpn(self.flabel), want,
                                          scope, facts))
            if joined is not None:
                return joined
        for text, how, line in step.requires:
            node = self.read(text)
            if self.term(node) == goal:
                # `side` is where a line is discharged by what it names, so
                # it is given `how` as well as the claim. A route reading
                # only the claim settles it from whatever the scope holds,
                # which is the proof not resting on the reason the page
                # gave.
                made = self.side(node, how, scope, facts, step)
                # A line that is there and whose justification does not
                # reach it is the text's to fix in the same way one that is
                # missing is. Handing the decline to the caller would put it
                # in a proof join, and say nothing about the line at fault.
                if declined(made):
                    raise self.defect(
                        self.at,
                        f'the requires line for {self.render(goal)} is '
                        f'justified by {how}, which does not reach it: {made}')
                return self.discharged_by(made, step, how, line)
        # A `requires` line that is not there is the text's to fix, so this
        # one is a defect. What it is built from declining is not, which is
        # why only a decline is turned into one here.
        found = self.settle(self.to_term(goal), scope, facts)
        if declined(found):
            raise self.defect(
                self.at, f'no requires line for {self.render(goal)}')
        return found

    def membership(self, said, system, scope, facts):
        """That a term belongs to a number system, which the text writes.

        `READERS.md` settles that membership is a dull fact the page states
        rather than a step's to discover, and records the price: ninety-seven
        such lines across the forty-two steps citing `algebra` or
        `inequalities`, the exemption having been rejected. So a term whose
        membership nothing supplies is a line the proof owes, and saying so
        is what this is for.

        The methods reach here for every atom they do not look inside, and
        they reach it while writing rather than while deciding. A decline
        given back from here would reach the caller as the method not
        covering the step, which is the one thing it does not mean.
        """
        want = self.seq(said, system, 'wcel')
        # What the step's own lines say, first. The scope may hold the same
        # claim with another origin — `abs-bounds` writes `requires x ∈ ℝ:
        # from H1` beside the hypothesis saying `x ∈ ℝ` — or a claim one
        # lemma away — `k ∈ ℤ` from the line that obtained k, where the step
        # wrote `k ∈ ℝ` and wants `k ∈ ℂ` — or the claim whole where the step
        # names only its parts, as the triangle inequality's step 5.2 names
        # `a ∈ ℝ` and `b ∈ ℝ` and line 1 says `a + b ∈ ℝ`. In each the line
        # the step names is the one to use; `part` says in what order.
        found = self.part(said, system, scope, facts)
        if not declined(found):
            return found
        # What `part` cannot build is searched for, with the step's own lines
        # laid over the scope's copies of the same claims. They replace those
        # copies and add almost nothing, so the search is no wider than it
        # was, and what it finds rests on the lines the step names.
        written = {k: v for k, v in facts.items() if from_requires(v)}
        for k, (at, v) in self.written.items():
            lifted = self.lifted_to(k, v, at, scope)
            if lifted is not None:
                written[k] = lifted
        found = self.settle(self.to_term(want), scope, {**facts, **written})
        if declined(found):
            raise self.defect(
                self.at, f'nothing says {self.render(want)}, which this step '
                         f'needs')
        return found

    def bridged(self, said, system, scope, written):
        """`said ∈ system`, carried in one lemma from a membership written.

        Only the lemmas `targets.MEMBERSHIP` declares that take a thing in
        one number system to another — `recn`, `zcn`, `nnre` — and only one
        of them. Settling from the written facts instead searches everything
        that could reach the claim, and where nothing written does, that
        search is what costs: `abs-bounds` spent four and a half million
        `fits` calls in it on one membership.
        """
        if self.bridges is None:
            self.bridges = {}
            for label in targets.MEMBERSHIP:
                sig = self.sigs.get(label)
                if sig is None or sig.essentials or len(sig.floats) != 1:
                    continue
                shape = self.syntax.statement(sig)
                if shape.label != 'wi':
                    continue
                given, gives = shape.children
                if given.label != 'wcel' or gives.label != 'wcel' \
                        or given.children[0].variable is None \
                        or given.children[0].rpn(self.flabel) \
                        != gives.children[0].rpn(self.flabel):
                    continue
                self.bridges.setdefault(
                    (given.children[1].rpn(self.flabel),
                     gives.children[1].rpn(self.flabel)), label)
        for (source, target), label in self.bridges.items():
            if target != system:
                continue
            claim = self.seq(said, source, 'wcel')
            proof = written.get(claim)
            if proof is None:
                held = self.written.get(claim)
                if held is not None:
                    proof = self.lifted_to(claim, held[1], held[0], scope)
            # What a requires line wrote, or what a line being cited says:
            # `requires |f(x₁) − f(c)| ∈ ℝ: thm:abs-real …, from 17.14` wants
            # the difference in ℂ and cites the line saying it is real, and
            # without this the lemmas were searched in their order, 25
            # seconds of it, to reach the same fact.
            origin = getattr(proof, 'origin', frozenset())
            if proof is None or not (from_requires(proof)
                                     or (origin and origin <= self.citing)):
                continue
            return self.ap('syl', {'ph': scope, 'ps': claim,
                                   'ch': self.seq(said, system, 'wcel')},
                           proof,
                           self.ap(label, {self.sigs[label].push[0]: said}))
        return None

    def built(self, said, system, scope, facts):
        """`said ∈ system` for a compound, from its parts; else a decline.

        A sum of reals is real by `readdcld` from its two parts being real,
        and each part is what the step's own line says of it where it wrote
        one. Searched for instead, `settle` tries its lemmas in their order
        and `zcn` comes before `mulcl`, so `a·x₀ ∈ ℂ` was reached through
        `a ∈ ℤ` from the hypothesis rather than through `a ∈ ℝ` from the line
        the page wrote. A fixed table and no search, so nothing it cannot
        build costs more than a lookup.
        """
        node = self.to_term(said)
        if node.variable is None and node.label == 'co' \
                and len(node.children) == 3:
            left, right, op = node.children
            op = op.rpn(self.flabel)
            lemma = CLOSED.get((op, system))
            if lemma is None:
                return Declined(f'no closure lemma for {op} in {system}')
            a, b = left.rpn(self.flabel), right.rpn(self.flabel)
            pa = self.part(a, system, scope, facts)
            if declined(pa):
                return pa
            pb = self.part(b, 'cn0' if op == 'cexp' else system, scope, facts)
            if declined(pb):
                return pb
            return self.ap(lemma, {'ph': scope, 'A': a,
                                   'N' if op == 'cexp' else 'B': b}, pa, pb)
        if node.variable is None and node.label == 'cneg' \
                and len(node.children) == 1:
            lemma = NEGATED.get(system)
            if lemma is None:
                return Declined(f'no closure lemma for negation in {system}')
            a = node.children[0].rpn(self.flabel)
            pa = self.part(a, system, scope, facts)
            if declined(pa):
                return pa
            return self.ap(lemma, {'ph': scope, 'A': a}, pa)
        return Declined('not a sum, difference, product, power or negation')

    def part(self, said, system, scope, facts):
        """One part of a compound, in a number system, or a decline.

        The step's own line first, then that line carried by one lemma, then
        the part built in turn if it is a compound. A numeral is the
        library's. What the scope holds is last, and only exactly: it is a
        line the page wrote, and a step using it without naming it is what
        provenance is there to see.
        """
        want = self.seq(said, system, 'wcel')
        found = facts.get(want)
        if found is not None and from_requires(found):
            return found
        held = self.written.get(want)
        if held is not None:
            lifted = self.lifted_to(want, held[1], held[0], scope)
            if lifted is not None:
                return lifted
        carried = self.bridged(said, system, scope, facts)
        if carried is not None:
            return carried
        term = self.to_term(said)
        if linear.numeral(term, self.flabel) is not None:
            return self.settle(self.to_term(want), scope, facts)
        made = self.built(said, system, scope, facts)
        if not declined(made):
            return made
        if found is not None:
            return found
        return Declined(f'nothing written says {self.render(want)}')

    def freeze(self, node):
        """The tree with its leaves turned into the terms they stand for.

        A definition's body is read with the definition's own names bound,
        and those names may be the ones the proof is using for something
        else: `def:odd` binds `k` and so does the step that obtains from it.
        Freezing the tree settles what it means before the names change
        back. A binder's own variable is left alone: it stands for itself,
        and the slot it fills wants the variable rather than a term saying
        what the variable means.
        """
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
    to come back the other way.
    """
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
        proof = work.seq(goal, proof, 'mptru')
    # What is written out is the proof's text, and this is where it stops
    # carrying what it rests on: everything that asked has asked.
    proof = proof.text

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
    held = {t for t in set(proof.split()) if t in sigs and sigs[t].kind == '$f'}
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
    label = label_of(thm.name, sigs, thm.path, thm.line)
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
    print(f'    {compress(proof, mandatory, {**sigs, **work.arities})} $.')
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

