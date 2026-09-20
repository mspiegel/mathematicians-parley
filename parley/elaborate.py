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
import re
import sys
import typing
from pathlib import Path

import field
import kernel
import linear
import targets
from formula import Grammar, Node, parse
from library import Signature
from library import read as read_library
from match import instantiation
from parse import Problem, check_encoding, citations, fmt, parse_database, parse_proof
from sorts import sorts_in_scope

LABEL = re.compile(r'\s*\([A-Z]+[0-9]*\)\s*$')
# `let A be a set` introduces a name the way `let n ∈ ℕ` does, and states
# what `A is a set` states. The hypothesis line reads better as it is
# written; the claim is the notation the database declares.
BE_A_SET = re.compile(r'\s+be\s+a\s+set\b')
CLASS_NAMES = ['cA', 'cB', 'cC', 'cD', 'cE', 'cF', 'cG', 'cH']
SPARE_VARS = ['vm', 'vk', 'vj', 'vi', 'vp', 'vq', 'vr', 'vs', 'vt', 'vu']
# The constructors that take a function, operation or relation as an operand.
WRAPS = ('co', 'wbr', 'cfv')


def seq(*parts):
    return ' '.join(p for p in parts if p)


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
    """A claim, a proof of it at one scope, and the tree it was read from."""

    def __init__(self, term, proof, node=None):
        self.term, self.proof, self.node = term, proof, node


class Block:
    """A block being elaborated: what it opened over and what it opened."""

    def __init__(self, owner, outer, facts, frame):
        self.owner, self.outer, self.outside = owner, outer, facts
        self.frame = frame          # index into the scope frames
        self.scope, self.facts = outer, facts
        self.supposed = None        # contradiction
        self.over = self.base = None                      # induction
        self.variable = None        # the setvar a fix introduced
        self.assumed = {}           # cases: part number -> what it assumes
        self.entered = None         # cases: the part now open
        self.claim = self.proof = None
        self.parts = {}             # part number -> the last fact in it


class Elaborator:
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
        ('wa', (0,)): 'anbi1d', ('wa', (1,)): 'anbi2d',
        ('wa', (0, 1)): 'anbi12d',
        ('w3a', (0,)): '3anbi1d', ('w3a', (1,)): '3anbi2d',
        ('w3a', (2,)): '3anbi3d', ('w3a', (0, 1, 2)): '3anbi123d',
        ('wn', (0,)): 'notbid',
        ('wral', (0,)): 'ralbidv', ('wrex', (0,)): 'rexbidv'}

    # Which transitivity folds one link of a calculation into the run above
    # it, by what each of the two claims is. Two relations in a row would
    # want the transitivity of that relation and no chain writes one.
    FOLDING: typing.ClassVar = {
        ('wceq', 'wceq'): 'eqtrd', ('wceq', 'wbr'): 'eqbrtrd',
        ('wbr', 'wceq'): 'breqtrd'}

    def __init__(self, thm, grammar, items, sigs, records, theorems=()):
        self.thm, self.g, self.items, self.sigs = thm, grammar, items, sigs
        self.terms = targets.terms(records)
        # A name the proof introduces becomes a variable of the kernel, and it
        # must not be one a notation's own target binds: `S(_)` sums over `k`,
        # so a proof that fixes `k` cannot be given `k`.
        self.taken = {t for entries in self.terms.values()
                      for e in entries if e for t in e.split()}
        self.spare = [v for v in SPARE_VARS if v not in self.taken]
        self.commutes = targets.commuting(records)
        self.syntax = kernel.Syntax(sigs)
        self.proofs = {t.name: t for t in theorems}
        self.cited = []          # corpus theorems this proof leans on
        self.joined = None
        self.enclosing = None    # the block a step sits directly inside
        self.shapes = {}         # target pattern -> the tree it reads as
        self.names = {}          # readable name -> kernel term
        self.sets = {}           # readable name -> the set it was let into
        self.axioms = []         # (label, statement) for each algebra step
        self.reserved = set()    # setvars the conclusion quantifies over
        self.bound_as = {}       # binder name -> the setvar it stands for
        self.assumed = {}        # statement -> how it is pushed, stated once
        self.last = None
        # A variable is pushed by the label of its floating hypothesis and
        # written by its own name, so both directions are wanted.
        self.flabel = {s.statement[1]: s.label for s in sigs.values()
                       if s.kind == '$f'}
        self.fname = {v: k for k, v in self.flabel.items()}
        self.forder = {s.label: i for i, s in enumerate(sigs.values())
                       if s.kind == '$f'}
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
        return parse(LABEL.sub('', text).strip(), self.g)

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
        return targets.fill(self.pattern(node), holes)

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

    def settle(self, wanted, scope, facts, depth=5):
        """A proof of something a step needs and the text does not write.

        A cited lemma asks side conditions of its own — that an index is in
        the upper integers, that a summand is complex — and those are not
        `requires` lines, because to a reader they are not steps. They are
        settled from the lemmas `targets.MEMBERSHIP` names, by matching what
        each concludes against what is wanted."""
        rpn = wanted.rpn(self.flabel)
        if rpn in facts:
            return facts[rpn]
        if depth > 0:
            if wanted.label in ('wa', 'w3a'):
                kids = [c.rpn(self.flabel) for c in wanted.children]
                return seq(scope, *kids,
                           *(self.settle(c, scope, facts, depth - 1)
                             for c in wanted.children),
                           'jca' if wanted.label == 'wa' else '3jca')
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
        is a last resort."""
        whole = self.syntax.statement(sig)
        if whole.label != 'wb':
            readings = [] if backwards else [((), whole, 'syl')]
        elif backwards:
            readings = [((whole.children[1],), whole.children[0], 'sylibr')]
        else:
            readings = [((whole.children[0],), whole.children[1], 'sylib')]
        for antecedents, reads, closing in readings:
            found = self.fitting(label, sig, whole, list(antecedents), reads,
                                 closing, wanted, scope, facts, depth)
            if found is not None:
                return found
        return None

    def fitting(self, label, sig, whole, antecedents, reads, closing,
                wanted, scope, facts, depth):
        """One reading of a lemma, applied to what is wanted.

        A lemma may ask more than one thing before it says anything —
        `ltle` wants both sides real and then the strict relation — so its
        antecedents are peeled until what is left is what is wanted."""
        variables = whole.names()
        binding = None
        while True:
            binding = kernel.match(reads, wanted, {}, variables)
            if binding is not None:
                break
            if reads.label != 'wi':
                return None
            antecedents.append(reads.children[0])
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

        pushed = [binding[v].rpn(self.flabel) if v in binding
                  else self.flabel[v] for v in sig.push]
        proof = seq(*pushed, label)
        if not antecedents:
            return seq(wanted.rpn(self.flabel), scope, proof, 'a1i')
        try:
            for i, slot in enumerate(antecedents):
                asks = slot.substitute(binding)
                rest = wanted.rpn(self.flabel)
                for later in reversed(antecedents[i + 1:]):
                    rest = seq(later.substitute(binding).rpn(self.flabel),
                               rest, 'wi')
                proof = seq(scope, asks.rpn(self.flabel), rest,
                            self.settle(asks, scope, facts, depth - 1), proof,
                            closing if i == 0 else 'mpd')
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
        return self.descend(self.shape(self.pattern(node)), holes, after,
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
        # A definition that introduces a name says which variable it takes;
        # one that does not leaves the lemma's own, which the match fixed.
        pushed = [var if v == sig.bound() and var is not None
                  else binding[v].rpn(self.flabel) if v in binding
                  else self.flabel[v]
                  for v in sig.push]
        # A lemma may state a condition in full rather than ask for it:
        # `elpw` wants what it is about to be a set before it will say what
        # belongs to its power class.
        pushed += [self.prove_essential(
            self.syntax.parse(e[1:], 'wff').substitute(binding), scope, facts)
            for e in sig.essentials]
        # The lemma unfolds to its own wording, which need not be the text's:
        # `divides` writes the product the other way round. What it gives is
        # built first, and the text's wording is reached from it.
        held = sig.bound()
        if held is not None and var is not None:
            binding[held] = kernel.Term(variable=self.sigs[var].statement[1])
        given = reads.children[1].substitute(binding).rpn(self.flabel)
        says = seq(left, given, 'wb')
        if not asks:
            proof = seq(says, scope, seq(*pushed, lemma), 'a1i')
        else:
            holds = asks[0].substitute(binding).rpn(self.flabel)
            proof = self.required(step, holds, over, scope, facts)
            for slot in asks[1:]:
                extra = slot.substitute(binding).rpn(self.flabel)
                proof = seq(scope, holds, extra, proof,
                            self.required(step, extra, over, scope, facts),
                            'jca')
                holds = seq(holds, extra, 'wa')
            proof = seq(scope, holds, says, proof, *pushed, lemma, 'syl')
        if ex is None or given == ex:
            return proof, given
        return seq(scope, left, given, ex, proof,
                   self.bridging(self.to_term(given), self.to_term(ex), scope,
                                 facts, step),
                   'bitrd'), ex

    def exchanged(self, given, want):
        """Whether these are one term with a commuting pair exchanged.

        `commutes` in `db/notation.db` is what says which operands may be,
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
            body = text[len(kind):] if text.startswith(kind) else text
            if kind == 'let' and BE_A_SET.search(body):
                body = BE_A_SET.sub(' is a set', body)
            node = self.read(body)
            if kind == 'let':
                introduced = self.subject_of(node)
                if introduced.text and introduced.text not in self.names:
                    self.names[introduced.text] = spare.pop(0)
                if node.notation == 'membership':
                    self.sets[introduced.text] = self.term(node.children[1])
            nodes.append(node)
        return nodes

    def defined(self):
        """Bind every name a `define` line introduces to what it stands for.

        A define is an abbreviation and nothing more: Cantor names a set B
        and every line about B is a line about the set-builder it names. So
        the name is bound to that term and the proof never carries it, which
        is also what keeps it apart from the B the conclusion quantifies
        over — those are two different things spelt the same way."""
        for _kind, text, label, line in self.thm.defines:
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
        or the lemma that generalises over one will find the other."""
        whole = self.to_term(rpn)
        binding = {}
        for said in sorted(whole.names()):
            label = self.flabel.get(said)
            if label and self.sigs[label].statement[0] == 'setvar':
                fresh = self.spare_var()
                binding[said] = kernel.Term(
                    variable=self.sigs[fresh].statement[1])
        return whole.substitute(binding).rpn(self.flabel)

    def run(self):
        nodes = self.hypotheses()
        self.defined()
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
        if head == 'contradiction':
            kind, text, label, _l, _p = step.openers[0]
            node = self.read(text[len(kind):] if text.startswith(kind)
                             else text)
            block.supposed = self.term(node)
            block.scope, block.facts = self.widen(scope, facts,
                                                  block.supposed)
            if label:
                lines[label] = Fact(block.supposed,
                                    block.facts[block.supposed], node)
            self.joined = None
        elif head == 'fix':
            block.scope, block.facts = scope, facts
            for kind, text, label, _l, _p in step.openers:
                body = text[len(kind):] if text.startswith(kind) else text
                if kind == 'let':
                    # A fixed name is a variable of the kernel, not a class,
                    # and it must avoid whatever the notations bind: the sum
                    # binds `k`, so a proof that fixes `k` cannot use it.
                    node = self.read(body)
                    name = node.children[0].text
                    block.variable = self.fixed_var(name)
                    self.names[name] = f'{block.variable} cv'
                    self.sets[name] = self.term(node.children[1])
                node = self.read(body)
                added = self.term(node)
                block.scope, block.facts = self.widen(block.scope,
                                                      block.facts, added)
                if label:
                    lines[label] = Fact(added, block.facts[added], node)
        elif head == 'cases':
            # Every other block opens one scope for all its children. A
            # `cases` opens one per part, so nothing is widened here and the
            # part is entered when its first child arrives.
            block.scope, block.facts = scope, facts
            block.assumed = {}
            for kind, text, label, _l, part in step.openers:
                body = text[len(kind):] if text.startswith(kind) else text
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
        node, label = block.assumed[part]
        assumed = self.term(node)
        block.scope, block.facts = self.widen(block.outer, block.outside,
                                              assumed)
        block.entered = part
        if label:
            lines[label] = Fact(assumed, block.facts[assumed], node)
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
        del self.frames[block.frame + 1:]
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
        """Induction closes with nnindd, which wants the claim five ways.

        The text writes none of them: it says only which name to induct on
        and where to start. So the claim is read as a function of that name
        and instantiated, and each instance is tied to the general one by
        congruence. `ELABORATION.md` requirement 13."""
        step, scope = block.owner, block.outer
        if set(block.parts) != {0, 1}:
            raise Problem('', step.line, 'induction wants a base and a step')
        (_base_claim, base), (step_claim, stepped) = (block.parts[0],
                                                      block.parts[1])
        name, general = block.over, f'{block.base} cv'
        at = re.search(r'starting at ([^\s,]+)', step.just.text)
        start = self.term(self.read(at.group(1))) if at else 'c1'
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
                  stepped, 'nnindd')
        if step_claim != reached:
            raise Problem('', step.line,
                          'the step does not reach the next instance')
        # nnindd states the membership apart from the rest of the antecedent,
        # and the scope already holds it, so the two are conjoined back.
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
        if head == 'obtain':
            return self.obtain(step, number, scope, facts, lines, closers)
        node = self.read(self.sentences(' '.join(step.claim))[-1])
        term = self.claim_of(' '.join(step.claim))
        how = {'algebra': self.algebra, 'arithmetic': self.arithmetic,
               'inequalities': self.inequalities,
               'substitute': self.substitute,
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
        lines[number] = Fact(term, proof, node)
        facts[term] = proof
        return scope, facts, closers

    # --- rendering ----------------------------------------------------------

    def render(self, rpn):
        """A term written the way a Metamath file writes it.

        Only generated axioms need this: a proof is written in the reverse
        Polish the kernel reads, but a `$a` states its claim in full."""
        stack = []
        for tok in rpn.split():
            sig = self.sigs[tok]
            count = len(sig.floats)
            args = stack[len(stack) - count:] if count else []
            del stack[len(stack) - count:]
            bound = dict(zip(sig.push, args, strict=True))
            stack.append(' '.join(bound.get(t, t) for t in sig.statement[1:]))
        return stack[0]

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
        named = re.search(r'\b((?:def|thm):\S+)', step.just.text)
        if named is None:
            raise Problem('', step.line,
                          'an obtain that names no item is not expanded')
        cites = step.just.text.split(':', 1)[1].strip()
        item = self.items[named.group(1).split(':', 1)[1]]

        saved = dict(self.names)
        if named.group(1).startswith('def:'):
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
        lines[number] = Fact(body, lifted[body])

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
        """What an item states, however the database says it is supplied."""
        for label in targets.clauses(item):
            found = self.apply_lemma(label, self.to_term(goal), scope, facts,
                                     step)
            if found is not None:
                return found
        return self.assume_item(step, goal, scope, facts, item, cites)

    def assume_item(self, step, goal, scope, facts, item, cites=None):
        """An item the database gives no target for, taken as it states itself.

        `thm:lowest-terms` is the case: set.mm has nothing of its shape, as
        `db/items.db` says, so what it claims is assumed under the hypotheses
        it asks for."""
        saved = dict(self.names)
        for name, value in instantiation(cites or step.just.text):
            self.names[name] = self.term(self.read(value))
        asks = []
        for kind, text, _label, _line in item.hypotheses:
            body = text[len(kind):] if text.startswith(kind) else text
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
        said = re.match(r'substitute\s+(.*)\s*\([^()]*\)'
                        r'(?:\s+into\s+(\S.*?))?\s*$', step.just.text)
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

        if said.group(2) is None:
            built, proof = self.rewrite(node.children[0], old, new, scope,
                                        facing)
            if built != self.term(node.children[1]):
                raise Problem('', step.line,
                              'the substitution misses the claim')
            return proof

        into = lines[said.group(2).split()[-1]]
        if into.node is None:
            raise Problem('', step.line,
                          f'{said.group(2)} is not a line to rewrite')
        # Which way the equation is used is whichever reaches what the step
        # claims. Cantor puts f(x) = B into a line saying x ∉ f(x) and into
        # another saying x ∉ B, and writes the equation once; and B holds an
        # f(x) of its own, under a name it binds, that neither touches.
        turned = seq(scope, old, new, facing, 'eqcomd')
        for was, now, faces in ((old, new, facing), (new, old, turned)):
            try:
                built, proof = self.rewrite(into.node, was, now, scope, faces)
            except Problem:
                continue
            if built == term:
                return seq(scope, into.term, term,
                           self.carried(said.group(2).split()[-1], facts,
                                        lines),
                           proof, 'mpbid')
        raise Problem('', step.line, 'the substitution misses the claim')

    def algebra(self, step, node, term, scope, facts, lines):
        """Decided by `parley/field.py`, and then taken.

        The same division of labour `inequalities` has: what the step claims
        is checked against what it cites, and a step that is not an identity
        of the field is refused rather than assumed. Emitting the proof of a
        decided step is what remains."""
        self.decide_field(step, term, lines)
        return self.assume(step, term, scope, facts, 'alg', lines)

    def decide_field(self, step, term, lines):
        """Refuse an `algebra` step that is not an identity.

        With nothing cited the claim must vanish outright; with equations
        cited it must be a combination of them. That the denominators are
        not zero is not decided here — the text writes those as `requires`
        lines, which is what `METHODS.md` means by them being hypotheses of
        the method."""
        claim = field.equation(self.to_term(term), self.flabel)
        if claim is None:
            return                               # not an equation this decides
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
        if not field.follows(given, claim, atoms):
            raise Problem('', step.line,
                          f'{self.render(term)} is not an identity, nor does '
                          f'it follow from what step {fmt(step.number)} '
                          f'cites')

    def arithmetic(self, step, node, term, scope, facts, lines):
        """Not expanded either. `METHODS.md` says it is closed numerals."""
        return self.assume(step, term, scope, facts, 'ari', lines)

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
        return self.assume(step, term, scope, facts, 'ine', lines)

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
                   self.settle(self.to_term(right), scope, facts), says,
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
        for ref in step.just.refs:
            cited = lines.get(ref)
            binding = cited and kernel.match(
                reads.children[0], self.to_term(cited.term), {}, variables)
            if binding:
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
        proof = seq(scope, left, right, self.carried(ref, facts, lines), says,
                    'mpbid')
        known = {right: proof}
        self.unpack(right, proof, scope, known)
        if term not in known:
            raise Problem('', step.line,
                          f'{lemma} does not say {self.render(term)}')
        return known[term]

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
        """A definition with no target is taken as it states itself."""
        return self.assume(step, term, scope, facts, 'def', lines)

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

    def apply_lemma(self, label, goal, scope, facts, step):
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
                return None
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
        pushed = [binding[v].rpn(self.flabel) if v in binding
                  else self.flabel[v] for v in sig.push]
        essentials = [self.prove_essential(
            self.syntax.parse(e[1:], 'wff').substitute(binding), where, known)
            for e in sig.essentials]
        proof = seq(*pushed, *essentials, label)
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
                    rest = seq(later.substitute(binding).rpn(self.flabel),
                               rest, join)
            first = proof.split()[-1] == label
            fold = {('wi', True): 'syl', ('wi', False): 'mpd',
                    ('wb', True): 'sylib', ('wb', False): 'mpbid'}
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
        try:
            return self.settle(self.to_term(term), scope, facts)
        except Problem:
            pass
        if want.notation == 'membership':
            return self.closure(want.children[0],
                                self.term(want.children[1]), scope, facts)
        closure = how.strip().split(',')[0].strip()
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
        """What stands where `mark` does, in a line shaped like the pattern.

        A cited line answers part of a claim rather than all of it — 3.14
        says 2 divides p, which is one of the three things 3.16 asks of d —
        so the search runs over the claim's parts, aligning each against the
        whole of the line. Alignment starts only at a part built the same
        way the line is, or the bare `d` inside a part would align with the
        line entire and the witness would come out as the line."""
        found = []
        if (pattern.label == actual.label
                and self.aligned(pattern, actual, mark, found) and found):
            return found[0]
        for child in pattern.children:
            got = self.witness_in(child, actual, mark)
            if got:
                return got
        return None

    def aligned(self, pattern, actual, mark, found):
        """Whether these agree everywhere but the marked place."""
        if pattern.rpn(self.flabel) == mark:
            here = actual.rpn(self.flabel)
            if found and found[0] != here:
                return False
            found[:] = [here]
            return True
        if pattern.variable is not None or actual.variable is not None:
            return pattern.variable == actual.variable
        if pattern.label != actual.label:
            return False
        if len(pattern.children) != len(actual.children):
            return False
        return all(self.aligned(a, b, mark, found)
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
            raise Problem('', step.line,
                          f'{step.just.head} has no target field')
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
            node = self.read(htext[len(kind):] if htext.startswith(kind)
                             else htext)
            if kind == 'let' and node.notation == 'membership':
                name = node.children[0].text
                self.names[name] = (self.term(self.read(written[name]))
                                    if name in written else spare.pop(0))
        wanted = [self.term(self.read(htext[len(kind):]
                                      if htext.startswith(kind) else htext))
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
        bound = self.binders.get(node.notation, ())
        return Node(node.notation, node.sort,
                    [c if i in bound else self.freeze(c)
                     for i, c in enumerate(node.children)], node.text)

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
    for path in sorted((root / 'db').glob('*.db')):
        rel = str(path.relative_to(root))
        records.extend(parse_database(rel, check_encoding(rel,
                                                          path.read_bytes())))
    theorems = []
    for path in sorted((root / 'proof').glob('*.proof')):
        rel = str(path.relative_to(root))
        theorems.extend(parse_proof(rel, check_encoding(rel,
                                                        path.read_bytes())))
    return records, theorems


def main(argv):
    if len(argv) < 3:
        print(__doc__.strip().splitlines()[-1], file=sys.stderr)
        return 2
    wanted, setmm = argv[1], argv[2]
    root = Path(__file__).resolve().parent.parent
    records, theorems = corpus(root)
    grammar = Grammar.load(records)
    items = {r.name: r for r in records
             if r.kind in ('definition', 'theorem')}
    found = [t for t in theorems if t.name == wanted]
    if not found:
        print(f'no theorem {wanted!r}', file=sys.stderr)
        return 2
    thm = found[0]
    sorts_in_scope(thm, grammar)
    sigs = read_library(setmm)

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
        print('   database gives no target for. $)')
    else:
        print('   Nothing here is assumed. $)')
    print()
    # A theorem this corpus proves is cited as one label, so the file that
    # elaborated it is read first and set.mm comes in through it.
    for name in work.cited:
        print(f'$[ {name}.mm $]')
    if not work.cited:
        print('$[ set.mm $]')
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

