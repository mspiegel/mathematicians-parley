"""Turn a readable proof into a Metamath proof.

This is the first elaborator and it covers one theorem. `ELABORATION.md` works
five proofs out by hand and lists what the expansion language has to have;
this implements that list for the methods `thm:odd-square` uses: `obtain`,
`substitute`, `calculation`, `algebra`, and a definition used to conclude an
existence claim.

Two things shape the code. A step is elaborated in deduction form, so every
line is an implication whose antecedent is the scope it sits in, and a step's
expansion is a function of the step and of that scope rather than of the step
alone. And the readable layer writes which side condition a step needs but
never how to prove it, so closure — that a product of integers is an integer,
that an integer is a complex number — is derived from the shape of the term.

`algebra` is not expanded. Each of its steps becomes an axiom stating what the
readable line claims under the `requires` lines it carries, which is what the
first hand elaboration did; `elaboration/build-parity.py` proves the two this
proof needs. Everything else here is built.

Usage:  tools/elaborate.py <theorem> <set.mm> [<proof file>]
"""
import re
import sys
import typing
from pathlib import Path

import targets
from formula import Grammar, Node, parse
from library import Signature
from library import read as read_library
from match import instantiation
from parse import Problem, check_encoding, parse_database, parse_proof
from sorts import sorts_in_scope

LABEL = re.compile(r'\s*\([A-Z]+[0-9]*\)\s*$')
CLASS_NAMES = ['cA', 'cB', 'cC', 'cD', 'cE', 'cF', 'cG', 'cH']
SPARE_VARS = ['vm', 'vk', 'vj', 'vi']


def seq(*parts):
    return ' '.join(p for p in parts if p)


class Fact:
    """A claim, a proof of it at one scope, and the tree it was read from."""

    def __init__(self, term, proof, node=None):
        self.term, self.proof, self.node = term, proof, node


class Elaborator:
    # Which lemma rewrites a subterm, by what encloses it and which hole it
    # sits in. The tree decides; nothing is searched for.
    CONGRUENCE: typing.ClassVar = {
        ('co', 0): 'oveq1d', ('co', 1): 'oveq2d',
        ('wbr', 0): 'breq1d', ('wbr', 1): 'breq2d',
        ('cfv', 0): 'fveq2d',
        ('wceq', 0): 'eqeq1d', ('wceq', 1): 'eqeq2d',
        ('wcel', 0): 'eleq1d', ('wcel', 1): 'eleq2d'}

    def __init__(self, thm, grammar, items, sigs):
        self.thm, self.g, self.items, self.sigs = thm, grammar, items, sigs
        self.names = {}          # readable name -> kernel term
        self.sets = {}           # readable name -> the set it was let into
        self.axioms = []         # (label, statement) for each algebra step
        self.spare = list(SPARE_VARS)
        self.last = None
        # A variable is pushed by the label of its floating hypothesis and
        # written by its own name, so both directions are wanted.
        self.flabel = {s.statement[1]: s.label for s in sigs.values()
                       if s.kind == '$f'}
        self.fname = {v: k for k, v in self.flabel.items()}
        # Which pattern of a record matched is read from the node's literal,
        # so a record's patterns are indexed by theirs, in declared order.
        self.literals = {}
        for n in grammar.notations:
            self.literals.setdefault(n.name, [])
            if n.literal not in self.literals[n.name]:
                self.literals[n.name].append(n.literal)

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
        operands, label, wrap, _slots = self.parts(node)
        return self.build(operands, label, wrap)

    def parts(self, node):
        """The operands a term is built from, what encloses them, and which
        operand each child is.

        A pattern may carry an operand the text never writes: `n²` carries the
        numeral 2 and `n is even` carries the 2 of `2 ∥ n`. So the operands are
        not always the children, and which operand a child is decides which
        congruence lemma rewrites inside it."""
        if node.notation == 'square':
            return [self.term(node.children[0]), 'c2'], 'cexp', 'co', [0]
        if node.notation == 'parity':
            even = ['c2', self.term(node.children[0])]
            if node.text == 'iseven':
                return even, 'cdvds', 'wbr', [1]
            return [self.build(even, 'cdvds', 'wbr')], 'wn', None, [None]
        if node.notation == 'there-is':
            body = self.term(node.children[2])
            return [body, 'v' + node.children[0].text,
                    self.term(node.children[1])], 'wrex', None, [None, 0, None]
        label, wrap = self.target(node.notation, node.text)
        kids = [self.term(c) for c in node.children]
        return kids, label, wrap, list(range(len(kids)))

    @staticmethod
    def build(operands, label, wrap):
        return (seq(*operands, label) if wrap is None
                else seq(*operands, label, wrap))

    def target(self, kind, literal):
        entries = targets.TERMS.get(kind)
        if not entries:
            raise Problem('', 0, f'no kernel target for notation {kind!r}')
        if len(entries) == 1:
            return entries[0]
        order = self.literals.get(kind, [])
        return entries[order.index(literal)] if literal in order else entries[0]

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

    # --- congruence ---------------------------------------------------------

    def rewrite(self, node, old, new, scope, eqproof):
        """A proof that `node` equals `node` with `old` replaced by `new`.

        The path from the root of the claim to the occurrence decides the
        lemmas, one per step along it, and which hole the occurrence sits in
        decides which lemma. Nothing is searched for."""
        if self.term(node) == old:
            return new, eqproof
        operands, label, wrap, slots = self.parts(node)
        for child, slot in zip(node.children, slots, strict=False):
            if slot is None or old not in self.term(child):
                continue
            inner, proof = self.rewrite(child, old, new, scope, eqproof)
            after = list(operands)
            after[slot] = inner
            rest = [k for j, k in enumerate(operands) if j != slot]
            # An operation or a relation is itself an operand of the lemma
            # that rewrites under it; a constructor that takes its arguments
            # directly is not.
            return self.build(after, label, wrap), \
                seq(scope, operands[slot], inner, *rest,
                    label if wrap else '', proof,
                    self.CONGRUENCE[(wrap or label, slot)])
        raise Problem('', 0, f'nothing to rewrite in {self.term(node)}')

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
        lemma, flipped = targets.UNFOLD[name]
        var = var or self.flabel[self.sigs[lemma].bound()]
        item = self.items[name.split(':', 1)[1]]
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
        closers = []
        for step in self.thm.steps:
            scope, facts, closers = self.step(step, scope, facts, lines,
                                              closers)

        goal = self.term(self.read(self.thm.conclusion))
        proof = lines[self.last].proof
        for close in reversed(closers):
            proof = close(proof, goal)
        return goal, terms, proof

    def step(self, step, scope, facts, lines, closers):
        head = step.just.head
        number = '.'.join(str(p) for p in step.number)
        self.last = number
        if head == 'obtain':
            return self.obtain(step, number, scope, facts, lines, closers)
        node = self.read(self.sentences(' '.join(step.claim))[-1])
        term = self.term(node)
        how = {'algebra': self.algebra, 'substitute': self.substitute,
               'calculation': self.calculation}.get(head)
        if how is None and head.startswith('def:'):
            how = self.conclude
        if how is None:
            raise Problem('', step.line, f'no expansion for {head!r}')
        proof = how(step, node, term, scope, facts, lines)
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
        written = re.match(r'substitute\s+(.*?)\s*\(', step.just.text).group(1)
        left, right = self.read(written).children
        old, new = self.term(left), self.term(right)
        held = facts.get(seq(new, old, 'wceq'))
        if held is None:
            raise Problem('', step.line, f'no equation {old} = {new} in scope')
        # The text writes `n = 2k + 1` and the kernel holds it the other way,
        # so the equation is turned round before it is used.
        facing = seq(scope, new, old, held, 'eqcomd')
        built, proof = self.rewrite(node.children[0], old, new, scope, facing)
        if built != self.term(node.children[1]):
            raise Problem('', step.line, 'the substitution misses the claim')
        return proof

    def algebra(self, step, node, term, scope, facts, lines):
        """Not expanded. The claim becomes an axiom under its own requires."""
        label = f'alg{len(self.axioms) + 1}'
        wants = [self.read(text) for text, _how, _line in step.requires]
        statement = term
        for want in reversed(wants):
            statement = seq(self.term(want), statement, 'wi')
        text = '|- ' + self.render(statement)
        self.axioms.append((label, text))
        free = [t for t in dict.fromkeys(text.split())
                if t in self.free_names()]
        self.sigs[label] = Signature(
            label, '$a', text.split(),
            [('setvar' if v.islower() else 'class', v) for v in free])
        proof = seq(*(('v' if v.islower() else 'c') + v for v in free), label)
        for want in wants:
            condition = self.term(want)
            proof = seq(scope, condition, term,
                        self.closure(want.children[0],
                                     self.term(want.children[1]), scope,
                                     facts),
                        proof, 'syl')
            term = seq(condition, term, 'wi')
        return proof

    def free_names(self):
        """Every kernel name in play, by the letter it is written with."""
        out = set()
        for term in list(self.names.values()):
            out.update(t[1:] for t in term.split() if t not in ('cv',))
        return out

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

    work = Elaborator(thm, grammar, items, sigs)
    goal, hypotheses, proof = work.run()
    antecedent = hypotheses[0]
    for extra in hypotheses[1:]:
        antecedent = seq(antecedent, extra, 'wa')

    print(f'$( {thm.name}, elaborated from {thm.path} by tools/elaborate.py.')
    print('   The algebra steps are axioms; everything else is built. $)')
    print()
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

