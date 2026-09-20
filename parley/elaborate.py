"""Turn a readable proof into a Metamath proof.

`ELABORATION.md` works five proofs out by hand and lists what the expansion
language has to have; this implements that list for the methods three of them
use. `obtain`, `contradiction`, `fix` and `induction` open scopes;
`substitute`, `calculation` and `join` are steps; a definition may be unfolded
or used to conclude an existence claim; and a theorem may be cited whether
set.mm supplies it or this corpus proves it.

Two things shape the code. A step is elaborated in deduction form, so every
line is an implication whose antecedent is the scope it sits in, and a step's
expansion is a function of the step and of that scope rather than of the step
alone. And the readable layer writes which side condition a step needs but
never how to prove it, so closure — that a product of integers is an integer,
that an integer is a complex number — is derived from the shape of the term.

What is not expanded is stated at the head of the file it writes: a closure
method, or a definition the database gives no target for. Each becomes an
axiom claiming exactly what the readable line claims, under the `requires`
lines that line carries.

Usage:  parley/elaborate.py <theorem> <set.mm>
"""
import re
import sys
import typing
from pathlib import Path

import kernel
import targets
from formula import Grammar, Node, parse
from library import Signature
from library import read as read_library
from match import instantiation
from parse import Problem, check_encoding, fmt, parse_database, parse_proof
from sorts import sorts_in_scope

LABEL = re.compile(r'\s*\([A-Z]+[0-9]*\)\s*$')
CLASS_NAMES = ['cA', 'cB', 'cC', 'cD', 'cE', 'cF', 'cG', 'cH']
SPARE_VARS = ['vm', 'vk', 'vj', 'vi', 'vp', 'vq', 'vr', 'vs', 'vt', 'vu']
# The constructors that take a function, operation or relation as an operand.
WRAPS = ('co', 'wbr', 'cfv')


def seq(*parts):
    return ' '.join(p for p in parts if p)


def label_of(name):
    """What this elaborator calls a theorem it has written out."""
    return name.replace('-', '')[:8]


def implication(words):
    """Split `( A -> B )` into A and B, or None if it is not one.

    set.mm writes every compound term in brackets, so the arrow that splits
    the whole is the one at depth zero."""
    if len(words) < 3 or words[0] != '(' or words[-1] != ')':
        return None
    depth = 0
    for i, word in enumerate(words[1:-1], 1):
        if word == '(':
            depth += 1
        elif word == ')':
            depth -= 1
        elif word == '->' and depth == 0:
            return words[1:i], words[i + 1:-1]
    return None


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
        ('csu', (0,)): 'sumeq1d'}

    def __init__(self, thm, grammar, items, sigs, records, theorems=()):
        self.thm, self.g, self.items, self.sigs = thm, grammar, items, sigs
        self.terms = targets.terms(records)
        # A name the proof introduces becomes a variable of the kernel, and it
        # must not be one a notation's own target binds: `S(_)` sums over `k`,
        # so a proof that fixes `k` cannot be given `k`.
        taken = {t for entries in self.terms.values() for e in entries if e
                 for t in e.split()}
        self.spare = [v for v in SPARE_VARS if v not in taken]
        self.syntax = kernel.Syntax(sigs)
        self.proofs = {t.name: t for t in theorems}
        self.cited = []          # corpus theorems this proof leans on
        self.joined = None
        self.enclosing = None    # the block a step sits directly inside
        self.shapes = {}         # target pattern -> the tree it reads as
        self.names = {}          # readable name -> kernel term
        self.sets = {}           # readable name -> the set it was let into
        self.axioms = []         # (label, statement) for each algebra step
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
            hole = re.search(r'hole\s+(\d+)', n.binds or '')
            if hole:
                self.binders[n.name] = int(hole.group(1)) - 1

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
        bound = self.binders.get(node.notation)
        holes = [self.flabel.get(c.text, 'v' + c.text) if i == bound
                 else self.term(c)
                 for i, c in enumerate(node.children)]
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
        """A proof that this term lies in `want`, from the shape of the term.

        The readable proof writes a `requires` line saying which fact it needs
        and which item supplies it. What it never writes is how to build that
        fact for a compound term, because to a reader that is not a step."""
        term = self.term(node)
        goal = seq(term, want, 'wcel')
        if goal in facts:
            return facts[goal]
        if node.notation == 'numeral':
            return seq(goal, scope,
                       node.text + targets.NUMERAL_IN[want], 'a1i')
        if node.notation == 'name':
            held = self.sets.get(node.text)
            lemma = targets.WIDEN.get((held, want))
            if not lemma or seq(term, held, 'wcel') not in facts:
                raise Problem('', 0, f'cannot put {node.text!r} in {want}')
            return seq(scope, seq(term, held, 'wcel'), goal,
                       facts[seq(term, held, 'wcel')], term, lemma, 'syl')
        lemma = targets.CLOSURE.get((want, node.notation))
        if not lemma:
            raise Problem('', 0, f'no closure lemma for {node.notation}')
        kids = [self.closure(c, want, scope, facts) for c in node.children]
        inner = [self.term(c) for c in node.children]
        if len(inner) == 1:                       # zsqcl, sqcl
            return seq(scope, seq(inner[0], want, 'wcel'), goal, kids[0],
                       inner[0], lemma, 'syl')
        pair = seq(*(seq(t, want, 'wcel') for t in inner), 'wa')
        return seq(scope, pair, goal,
                   seq(scope, *(seq(t, want, 'wcel') for t in inner), *kids,
                       'jca'),
                   *inner, lemma, 'syl')

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
            if wanted.label == 'wa':
                left, right = wanted.children
                return seq(scope, left.rpn(self.flabel),
                           right.rpn(self.flabel),
                           self.settle(left, scope, facts, depth - 1),
                           self.settle(right, scope, facts, depth - 1), 'jca')
            for label in targets.MEMBERSHIP:
                sig = self.sigs.get(label)
                if sig is None or sig.essentials:
                    continue
                found = self.fits(label, sig, wanted, scope, facts, depth)
                if found is not None:
                    return found
        raise Problem('', 0, f'cannot settle {self.render(rpn)}')

    def fits(self, label, sig, wanted, scope, facts, depth):
        """Whether one lemma settles what is wanted, and how.

        A lemma may ask more than one thing before it says anything —
        `ltle` wants both sides real and then the strict relation — so its
        antecedents are peeled until what is left is what is wanted."""
        whole = self.syntax.statement(sig)
        variables = whole.names()
        antecedents, reads, closing = [], whole, 'syl'
        if whole.label == 'wb':
            antecedents, reads, closing = [whole.children[0]], \
                whole.children[1], 'sylib'
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
        holes = [self.term(c) for c in node.children]
        after, proofs = list(holes), {}
        for i, child in enumerate(node.children):
            if old not in self.term(child):
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
        """Name every `let` variable, and read the hypotheses."""
        nodes, spare = [], list(CLASS_NAMES)
        for kind, text, _label, _line in self.thm.hypotheses:
            node = self.read(text[len(kind):] if text.startswith(kind)
                             else text)
            if kind == 'let' and node.notation == 'membership':
                name = node.children[0].text
                self.names[name] = spare.pop(0)
                self.sets[name] = self.term(node.children[1])
            nodes.append(node)
        return nodes

    def run(self):
        nodes = self.hypotheses()
        terms = [self.term(n) for n in nodes]
        scope = terms[0]
        facts = {terms[0]: seq(scope, 'id')}
        for extra in terms[1:]:
            wider = seq(scope, extra, 'wa')
            facts = {k: seq(wider, scope, k, seq(scope, extra, 'simpl'), v,
                            'syl')
                     for k, v in facts.items()}
            facts[extra] = seq(scope, extra, 'simpr')
            scope = wider

        lines = {h[2]: Fact(t, facts[t])
                 for h, t in zip(self.thm.hypotheses, terms, strict=True)}
        self.frames = [(scope, None, facts)]
        closers, blocks = [], []
        for step in self.thm.steps:
            # A block's children are the steps numbered below it, so the
            # block closes at the first step that is not one of them.
            while blocks and len(step.number) <= len(blocks[-1].owner.number):
                done = blocks.pop()
                scope, facts = self.close_block(done, facts, lines)
                self.hand_up(done, blocks)
            if step.openers or step.parts:
                block = self.open_block(step, scope, facts, lines)
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
            scope, facts = self.close_block(done, facts, lines)
            self.hand_up(done, blocks)

        goal = self.claim_of(self.thm.conclusion)
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
        # Each frame keeps what is known at it, because a step whose lemma
        # forbids an inner assumption is proved at an outer one.
        self.frames.append((inner, added, lifted))
        return inner, lifted

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
                    block.variable = self.spare.pop(0)
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
            block.base = self.spare.pop(0)
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

    def close_block(self, block, facts, lines):
        """What a block gives back, by the lemma its kind closes with."""
        step = block.owner
        head = step.just.head
        del self.frames[block.frame + 1:]
        if head == 'contradiction':
            block.claim, block.proof = self.close_contradiction(block, facts)
        elif head == 'fix':
            held = lines[self.last]
            block.claim, block.proof = held.term, held.proof
            return block.outer, block.outside     # the induction takes it
        elif head == 'cases':
            block.claim, block.proof = self.close_cases(block, lines)
        elif head == 'induction':
            block.claim, block.proof = self.close_induction(block, lines)
        number = '.'.join(str(p) for p in step.number)
        outer = dict(block.outside)
        outer[block.claim] = block.proof
        lines[number] = Fact(block.claim, block.proof)
        self.last = number
        return block.outer, outer

    def close_contradiction(self, block, facts):
        """A contradiction closes on the pair its `join` named.

        pm2.65d takes the supposition implying a claim and the supposition
        implying its negation, and gives the supposition negated. The join
        itself emits nothing: this consumes both lines."""
        step, scope, supposed = block.owner, block.outer, block.supposed
        if not self.joined:
            raise Problem('', step.line, 'the block closes on no join')
        first, second = self.joined
        if second != seq(first, 'wn'):
            first, second = second, first
        if second != seq(first, 'wn'):
            raise Problem('', step.line,
                          'the joined lines are not a contradiction')
        claim = self.claim_of(' '.join(step.claim))
        return claim, seq(scope, supposed, first,
                          seq(scope, supposed, first, facts[first], 'ex'),
                          seq(scope, supposed, second, facts[second], 'ex'),
                          'pm2.65d')

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
        held = lines[step.just.refs[0]]
        return claim, seq(scope, first, claim, second, *said, held.proof,
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
        variable = block.variable or f'{self.spare.pop(0)}'
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
               'calculation': self.calculation, 'join': self.join}.get(head)
        if how is None and head.startswith('def:'):
            item = self.items[head.split(':', 1)[1]]
            # A definition stated as a biconditional is used by unfolding it;
            # one stated as an equation is used by citing the lemma that
            # proves it. With no target it is taken as stated, like a closure
            # method, and listed at the file's head.
            if 'target' not in item.fields:
                how = self.take_definition
            elif any('↔' in text for text, _line in item.conclusions):
                how = self.conclude
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
        """A name introduced from a definition, which opens a scope.

        This is the step that changes the shape of every step after it. The
        existential a definition supplies is not something the kernel can hand
        a name out of, so everything below is proved as the body of an
        implication and the existential is discharged at the very end."""
        got = re.match(r'obtain\s+([^\s:,]+)', step.just.text).group(1)
        name = re.search(r'\b(def:\S+)', step.just.text).group(1)
        cites = step.just.text.split(':', 1)[1].strip()   # past `obtain k:`
        subject = self.names[instantiation(cites)[0][1]]
        saved = dict(self.names)
        lemma, var, kernel, _text, over, left = self.definition(name, subject)
        body = self.term(kernel)
        self.names = saved
        ex = seq(body, var, over, 'wrex')

        source = seq(subject, over, 'wcel')
        p_ex = seq(scope, left, ex, facts[left],
                   seq(scope, source, seq(left, ex, 'wb'), facts[source],
                       var, subject, lemma, 'syl'),
                   'mpbid')

        member = seq(f'{var} cv', over, 'wcel')
        outer = seq(scope, member, 'wa')
        inner = seq(outer, body, 'wa')
        p_outer = seq(inner, body, 'simpl') if False else \
            seq(outer, body, 'simpl')
        p_scope = seq(inner, outer, scope, p_outer,
                      seq(scope, member, 'simpl'), 'syl')
        lifted = {k: seq(inner, scope, k, p_scope, v, 'syl')
                  for k, v in facts.items()}
        lifted[member] = seq(inner, outer, member, p_outer,
                             seq(scope, member, 'simpr'), 'syl')
        lifted[body] = seq(outer, body, 'simpr')

        self.names[got] = f'{var} cv'
        self.sets[got] = over
        lines[number] = Fact(body, lifted[body], kernel)

        def close(proof, goal):
            return seq(scope, ex, goal, p_ex,
                       seq(scope, body, goal, var, over,
                           seq(outer, body, goal, proof, 'ex'), 'rexlimdva'),
                       'mpd')

        return inner, lifted, [*closers, close]

    def substitute(self, step, node, term, scope, facts, lines):
        """One equation put into one claim, at the place the tree names."""
        # The reference is the bracket at the end; the equation may hold
        # brackets of its own, as `S(k) = k(k + 1)/2` does.
        written = re.match(r'substitute\s+(.*)\s*\([^()]*\)\s*$',
                           step.just.text).group(1)
        left, right = self.read(written).children
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
        built, proof = self.rewrite(node.children[0], old, new, scope, facing)
        if built != self.term(node.children[1]):
            raise Problem('', step.line, 'the substitution misses the claim')
        return proof

    def algebra(self, step, node, term, scope, facts, lines):
        """Not expanded. The claim becomes an axiom under its own requires."""
        return self.assume(step, term, scope, facts, 'alg')

    def arithmetic(self, step, node, term, scope, facts, lines):
        """Not expanded either. `METHODS.md` says it is closed numerals."""
        return self.assume(step, term, scope, facts, 'ari')

    def inequalities(self, step, node, term, scope, facts, lines):
        """Not expanded. Its steps rewrite by a cited equation as well as
        chain relations, and nothing here does the first."""
        return self.assume(step, term, scope, facts, 'ine')

    def take_definition(self, step, node, term, scope, facts, lines):
        """A definition with no target is taken as it states itself."""
        return self.assume(step, term, scope, facts, 'def')

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
        """Apply one set.mm lemma to reach a claim, side conditions and all."""
        sig = self.sigs[label]
        whole = self.syntax.statement(sig)
        variables = whole.names()
        antecedents, reads, binding = [], whole, None
        while True:
            binding = kernel.match(reads, goal, {}, variables)
            if binding is not None:
                break
            if reads.label != 'wi':
                return None
            antecedents.append(reads.children[0])
            reads = reads.children[1]

        # The scope is where a lemma's disjointness conditions can forbid it,
        # so it is chosen before anything is built. ELABORATION.md 14.
        where, frame = self.allowed(sig, binding, variables)
        known = self.frames_facts(frame, facts)
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
        for slot in antecedents:
            asks = slot.substitute(binding)
            if asks.rpn(self.flabel) == where:
                continue                      # the deduction slot
            rest = goal.rpn(self.flabel)
            for later in reversed(antecedents[antecedents.index(slot) + 1:]):
                if later.substitute(binding).rpn(self.flabel) != where:
                    rest = seq(later.substitute(binding).rpn(self.flabel),
                               rest, 'wi')
            proof = seq(where, asks.rpn(self.flabel), rest,
                        self.settle(asks, where, known), proof,
                        'syl' if proof.split()[-1] == label else 'mpd')
        return self.carry(proof, goal.rpn(self.flabel), frame)

    def prove_essential(self, want, scope, facts):
        """One hypothesis a lemma states in full rather than asking for."""
        if want.label != 'wi':
            return self.settle(want, scope, facts)
        left, right = want.children
        under = left.rpn(self.flabel)
        if under == right.rpn(self.flabel):
            return seq(under, 'id')
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

    def assume(self, step, term, scope, facts, prefix):
        """State what a step claims, under the conditions it writes, and
        take it. What the file assumes is listed at its head."""
        label = self.fresh(prefix)
        wants = [self.read(text) for text, _how, _line in step.requires]
        statement = term
        for want in reversed(wants):
            statement = seq(self.term(want), statement, 'wi')
        text = '|- ' + self.render(statement)
        self.axioms.append((label, text))
        # What a statement asks to be pushed is every variable it mentions,
        # in the order the database declares them, which is not the order the
        # statement happens to write them in.
        free = sorted({t for t in text.split() if t in self.flabel},
                      key=lambda v: self.forder[self.flabel[v]])
        self.sigs[label] = Signature(
            label, '$a', text.split(),
            [(self.sigs[self.flabel[v]].statement[0], v) for v in free])
        proof = seq(*(self.flabel[v] for v in free), label)
        if not wants:
            # Nothing to discharge, so the statement is simply taken at the
            # scope the step sits in.
            return seq(term, scope, proof, 'a1i')
        # The conditions nest, outermost first, so each is answered in turn
        # and what is left of the statement shrinks by one.
        for i, (want, (_t, how, _l)) in enumerate(zip(wants, step.requires,
                                                      strict=True)):
            rest = term
            for later in reversed(wants[i + 1:]):
                rest = seq(self.term(later), rest, 'wi')
            proof = seq(scope, self.term(want), rest,
                        self.side(want, how, scope, facts), proof,
                        'syl' if i == 0 else 'mpd')
        return proof

    def fresh(self, prefix):
        """A label for a generated statement that set.mm is not using.

        `ine1` reads as the first inequality this file assumes; set.mm reads
        it as `_i =/= 1`. The library is large enough that a short name is
        never safely free, so one is looked for."""
        number = len(self.axioms) + 1
        while f'{prefix}{number}' in self.sigs:
            number += 1
        return f'{prefix}{number}'

    def side(self, want, how, scope, facts):
        """A proof of what one `requires` line asks for."""
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
        if how.strip().startswith('arithmetic'):
            label = self.fresh('ari')
            self.axioms.append((label, '|- ' + self.render(term)))
            self.sigs[label] = Signature(label, '$a',
                                         ['|-', *self.render(term).split()])
            return seq(term, scope, label, 'a1i')
        raise Problem('', 0, f'cannot supply {self.render(term)}')

    def calculation(self, step, node, term, scope, facts, lines):
        """A chain of equalities folded by transitivity, one link at a time."""
        links = [text.rsplit(None, 1) for text, _line in step.just.chain]
        start, run = self.read(links[0][0]).children
        left, right = self.term(start), self.term(run)
        proof = lines[links[0][1]].proof
        for body, cite in links[1:]:
            nxt = self.term(self.read(body.lstrip('= ')))
            proof = seq(scope, left, right, nxt, proof, lines[cite].proof,
                        'eqtrd')
            right = nxt
        return proof

    def conclude(self, step, node, term, scope, facts, lines):
        """A definition used the other way: to conclude an existence claim.

        The witness is never written in the text. It is read off the cited
        line, by walking the shape the definition states against it."""
        subject = self.term(self.read(instantiation(step.just.text)[0][1]))
        var = self.spare.pop(0)
        saved = dict(self.names)
        bound = self.items[step.just.head.split(':', 1)[1]]
        lemma, var, kernel, written, over, _left = self.definition(
            step.just.head, subject, var=var)
        # Where the bound name sits in the definition's own body is read
        # while the definition's names are in force; what stands there is
        # read from the cited line once the proof's names are back.
        place = self.path_to(written,
                             self.read(bound.conclusions[0][0])
                             .children[1].children[0].text)
        kernel = self.freeze(kernel)
        self.names = saved

        cited = lines[step.just.refs[0]]
        if place is None:
            raise Problem('', step.line, 'the definition binds nothing')
        witness = self.term(self.at(cited.node, place))
        body = self.term(kernel)
        here = self.term(self.substituted(kernel, f'{var} cv', witness))
        at = seq(f'{var} cv', witness, 'wceq')
        _built, instance = self.rewrite(kernel, f'{var} cv', witness, at,
                                        seq(at, 'id'))

        ex = seq(body, var, over, 'wrex')
        member = seq(witness, over, 'wcel')
        p_member = self.required(step, member, over, scope, facts)
        # The cited line faces the way the text writes the definition, and
        # the existential faces the way the lemma writes it.
        p_cited = cited.proof
        if cited.term != here:
            p_cited = seq(scope, *(self.term(c) for c in cited.node.children),
                          cited.proof, 'eqcomd')
        p_ex = seq(scope, seq(member, here, 'wa'), ex,
                   seq(scope, member, here, p_member, p_cited, 'jca'),
                   body, here, var, witness, over, instance, 'rspcev', 'syl')

        holds = seq(subject, over, 'wcel')
        p_subject = self.required(step, holds, over, scope, facts)
        return seq(scope, term, ex, p_ex,
                   seq(scope, holds, seq(term, ex, 'wb'), p_subject,
                       var, subject, lemma, 'syl'),
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
        held = {lines[ref].term: lines[ref].proof for ref in step.just.refs}
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
        label = targets.lemma(item)[0]
        if not label:
            raise Problem('', step.line,
                          f'{step.just.head} has no target field')
        found = self.apply_lemma(label, self.to_term(term), scope, facts,
                                 step)
        if found is None:
            raise Problem('', step.line,
                          f'{label} does not reach what step '
                          f'{fmt(step.number)} claims')
        return found

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
        return seq(scope, pair, term, proof, *pushed, label_of(item.name),
                   'syl')

    def stating(self, wanted, facts):
        """The term in scope that says this, found by what it reads as."""
        for held in facts:
            if self.render(held) == wanted:
                return held
        raise Problem('', 0, f'nothing in scope states {wanted}')

    def required(self, step, goal, want, scope, facts):
        """The `requires` line that supplies one side condition."""
        if goal in facts:
            return facts[goal]
        for text, _how, _line in step.requires:
            node = self.read(text)
            if self.term(node) == goal:
                return self.closure(node.children[0], want, scope, facts)
        raise Problem('', step.line, f'no requires line for {goal}')

    def find(self, pattern, actual, bound):
        """What stands where the definition's bound name does."""
        if self.term(pattern) == bound:
            return self.term(actual)
        for p, a in zip(pattern.children, actual.children, strict=False):
            got = self.find(p, a, bound)
            if got is not None:
                return got
        return None

    def freeze(self, node):
        """The tree with its leaves turned into the terms they stand for.

        A definition's body is read with the definition's own names bound,
        and those names may be the ones the proof is using for something
        else: `def:odd` binds `k` and so does the step that obtains from it.
        Freezing the tree settles what it means before the names change
        back."""
        if not node.children:
            return _Literal(self.term(node))
        return Node(node.notation, node.sort,
                    [self.freeze(c) for c in node.children], node.text)

    @staticmethod
    def path_to(node, name):
        """Where a name sits in a tree, as a list of child indexes."""
        if node.notation == 'name' and node.text == name:
            return []
        for i, child in enumerate(node.children):
            found = Elaborator.path_to(child, name)
            if found is not None:
                return [i, *found]
        return None

    @staticmethod
    def at(node, path):
        for i in path:
            node = node.children[i]
        return node

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
    antecedent = hypotheses[0]
    for extra in hypotheses[1:]:
        antecedent = seq(antecedent, extra, 'wa')

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
    label = thm.name.replace('-', '')[:8]
    print(f'  {label} $p |- ( {work.render(antecedent)} -> '
          f'{work.render(goal)} ) $=')
    print(f'    {proof} $.')
    print('$}')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))

