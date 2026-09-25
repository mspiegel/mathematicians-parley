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
from matcher import Matcher
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
from provenance import ProofRules
from reading import CLASS_NAMES, Reading, hypothesis_body, render
from scopes import Fact, Scopes
from sorts import sorts_in_scope
from spell import Builder, seq
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


class Elaborator(Reading, Scopes, Matcher, TableReading, Calculators,
                 ProofRules, Builder):
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
        self.lemma_heads = None  # declared lemma -> what its readings end on
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
        # The scope frames, innermost last, each (scope, what it added, what
        # is known there); `run` opens the outermost at the hypotheses.
        self.frames = []
        self.lines = {}          # line label -> the Fact it proved
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

        alike = self.congruence(old, new, scope, {}, None,
                                self.closing(('spelt',)))
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
        known = self.supplied(step, scope, facts) if step.requires else {}
        citing, self.citing = self.citing, frozenset(step.just.refs)
        try:
            with self.writing(scope, known, keep=True):
                proof = how(step, node, term, scope, facts, lines)
        finally:
            self.citing = citing
        # Every route the method had declined, so nothing here owns the
        # step. That is this elaborator's limit rather than a defect in the
        # text, and it is said here because here is where the step is.
        if declined(proof):
            raise self.defect(step.line,
                              f'no method owns this step: {proof}')
        if proof is None:                  # a join, which emits nothing
            return scope, facts, closers
        said = self.said(step)
        proof = self.check_step(proof, step, number)
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
        asks = []
        with self.names_kept():
            for name, node in self.item_binding(step, item, cites).items():
                self.names[name] = self.term(node)
            with self.in_its_names(item):
                for kind, text, _label, _line in item.hypotheses:
                    body = hypothesis_body(kind, text)
                    asks.append(self.term(self.read(body)))
                ends = [self.term(self.read(text))
                        for text, _line in item.conclusions]

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
            if whole.label in rules.INSTANCES:
                body, variable, *over = whole.children
                lemma, slot, domain = rules.INSTANCES[whole.label]
                domain = domain or over[0].rpn(self.flabel)
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

        with self.names_kept():
            self.names[said] = stands
            shape = self.freeze(node.children[2])
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
        with self.names_kept():
            # A definition may name more than the thing it is about:
            # `def:stdlib/divisibility/divides` is about d and says what it
            # divides, and the step fills in both.
            for name, value in instantiation(step.just.text):
                self.names[name] = self.term(self.read(value))
            lemma, var, kernel, _w, over, _left = self.definition(
                step.just.head, subject, var=var)
            kernel = self.freeze(kernel)

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
        with self.names_kept():
            for name, value in instantiation(cites or step.just.text):
                self.names[name] = self.term(self.read(value))
            return {name: self.to_term(self.term(self.read(formula)))
                    for name, formula in fills.items()}

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
        spare = list(CLASS_NAMES)
        written = dict(instantiation(cites or step.just.text))
        binds = {}
        with self.names_kept(sets=True) as saved:
            for kind, htext, _label, _line in other.hypotheses:
                node = self.read(hypothesis_body(kind, htext))
                # `let X be a set` names a class as surely as `let n ∈ ℕ`
                # does; `hypothesis_body` has already turned it into the
                # formula that says so, and the name is in the same place.
                # `let a ∉ X` reads as a conjunction whose first leaf is the
                # name.
                if kind == 'let' and node.notation in ('membership',
                                                       'is-a-set',
                                                       'conjunction'):
                    name = self.subject_of(node).text
                    theirs = spare.pop(0)
                    # A hypothesis the citation does not name stands for
                    # what the citing proof calls by the same word. Bezout
                    # cites this theorem as `c := a` and says nothing of a,
                    # b, d, x₀ or y₀, because it holds names spelt that way
                    # and those are the ones it means. A word it does not
                    # hold takes a spare.
                    if name in written:
                        self.names[name] = self.term(self.read(written[name]))
                    elif name not in saved:
                        self.names[name] = theirs
                    binds[theirs] = self.names[name]
            wanted = [self.term(self.read(hypothesis_body(kind, htext)))
                      for kind, htext, _l, _n in other.hypotheses]
            # The step may claim one sentence of a conclusion that says
            # several: `thm:proof/triangle-inequality/abs-bounds` concludes
            # x ≤ |x| and −x ≤ |x|, and a step that needs only the first
            # says only the first. The theorem gives the whole, read in its
            # own sorts, and the sentence is taken out of it.
            whole = term
            if (len(self.sentences(other.conclusion))
                    > len(self.sentences(' '.join(step.claim)))):
                with self.in_its_names(other):
                    whole = self.claim_of(other.conclusion)

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

