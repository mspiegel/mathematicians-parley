"""Read a set.mm statement as a term.

A proof is written in reverse Polish and a statement is written in full, and
the elaborator needs to go between them. Turning a term into a statement is
substitution, and `elaborate.py` does it directly; turning a statement into a
term is parsing, and set.mm's syntax axioms are the grammar. They are an
ordinary context-free grammar — 1,472 productions, none longer than sixteen
symbols — so this is an ordinary chart parse.

What it buys is that a lemma can be matched rather than described. Without it
the database would have to say which of a lemma's variables each part of a
readable statement fills, and what each of its essential hypotheses asks for.
With it, the lemma's own statement says both.

A statement writes its parts in reading order and a proof pushes them in the
order the database declares them, which is not the same: `( A F B )` reads A,
F, B and pushes A, B, F. So each rule carries the permutation between them.
"""
from parse import Problem

TYPECODES = ('wff', 'class', 'setvar')


class Rule:
    """One syntax axiom, as a production of the grammar."""

    __slots__ = ('label', 'order', 'symbols', 'yields')

    def __init__(self, label, yields, symbols, order):
        self.label, self.yields = label, yields
        self.symbols = symbols     # ('t', token) or ('n', typecode)
        self.order = order         # push position of each part, in reading order


class Term:
    """A parsed statement: a constructor applied to terms, or a variable."""

    __slots__ = ('children', 'label', 'variable')

    def __init__(self, label=None, children=(), variable=None):
        self.label, self.children, self.variable = label, children, variable

    def rpn(self, labels):
        """The term as a proof writes it, pushing what each label wants."""
        if self.variable is not None:
            return labels[self.variable]
        return ' '.join([*(c.rpn(labels) for c in self.children), self.label])

    def names(self):
        if self.variable is not None:
            return {self.variable}
        return set().union(set(), *(c.names() for c in self.children))

    def substitute(self, binding):
        if self.variable is not None:
            return binding.get(self.variable, self)
        return Term(self.label,
                    tuple(c.substitute(binding) for c in self.children))


def match(pattern, ground, binding, variables):
    """Bind the pattern's variables so that it becomes the ground term."""
    if pattern.variable is not None and pattern.variable in variables:
        seen = binding.get(pattern.variable)
        if seen is not None:
            return binding if _same(seen, ground) else None
        out = dict(binding)
        out[pattern.variable] = ground
        return out
    if pattern.variable is not None or ground.variable is not None:
        return binding if pattern.variable == ground.variable else None
    if pattern.label != ground.label:
        return None
    if len(pattern.children) != len(ground.children):
        return None
    for a, b in zip(pattern.children, ground.children, strict=True):
        binding = match(a, b, binding, variables)
        if binding is None:
            return None
    return binding


def _same(a, b):
    if a.variable is not None or b.variable is not None:
        return a.variable == b.variable
    return (a.label == b.label and len(a.children) == len(b.children)
            and all(_same(x, y) for x, y in zip(a.children, b.children,
                                                strict=True)))


class Syntax:
    """set.mm's syntax axioms, ready to parse with."""

    def __init__(self, signatures):
        self.rules, self.by_yield = [], {t: [] for t in TYPECODES}
        self.typecode, self.label = {}, {}
        # A statement spells one term and an elaborator reads the same few
        # statements over and over: settling a side condition tries every
        # lemma it is allowed to try, and each is a chart parse. So what a
        # run of tokens spells is worked out once.
        self.spelt = {}
        for sig in signatures.values():
            if sig.kind == '$f':
                self.typecode[sig.statement[1]] = sig.statement[0]
                self.label[sig.statement[1]] = sig.label
        for sig in signatures.values():
            if sig.kind != '$a' or sig.statement[0] not in TYPECODES:
                continue
            symbols, reading = [], []
            for token in sig.statement[1:]:
                kind = self.typecode.get(token)
                symbols.append(('n', kind) if kind else ('t', token))
                if kind:
                    reading.append(token)
            order = [reading.index(v) for v in sig.push] if reading else []
            rule = Rule(sig.label, sig.statement[0], symbols, order)
            self.rules.append(rule)
            self.by_yield[rule.yields].append(rule)

    def build(self, rule, parts):
        """One rule's match, with its parts put in push order."""
        return Term(rule.label, tuple(parts[i] for i in rule.order))

    def parse(self, tokens, start='wff'):
        """The term these tokens spell, or a Problem if they spell none."""
        tokens = list(tokens)
        key = (tuple(tokens), start)
        held = self.spelt.get(key)
        if held is not None:
            return held
        found = self.spell(tokens, start)
        self.spelt[key] = found
        return found

    def spell(self, tokens, start):
        """What these tokens spell, worked out rather than remembered."""
        # A statement may be one variable and nothing else, which no rule
        # produces: `vtocl3` concludes `ps`.
        if len(tokens) == 1 and self.typecode.get(tokens[0]) == start:
            return Term(variable=tokens[0])
        n = len(tokens)
        chart = [{} for _ in range(n + 1)]
        # What has been offered at a position, so it is offered once. set.mm
        # has hundreds of productions yielding `class`, and every item
        # waiting for one would otherwise offer them all again: the second
        # offer adds nothing, because the row already holds every one of
        # them, and the work of finding that out is most of the parse.
        told = {(0, start)}
        for rule in self.by_yield[start]:
            _add(chart[0], rule, 0, 0, ())
        for i in range(n + 1):
            queue, seen = list(chart[i].values()), 0
            while seen < len(queue):
                rule, dot, origin, parts = queue[seen]
                seen += 1
                if dot == len(rule.symbols):
                    made = self.build(rule, parts)
                    for older in list(chart[origin].values()):
                        orule, odot, oorigin, oparts = older
                        if odot == len(orule.symbols):
                            continue
                        kind, what = orule.symbols[odot]
                        if kind != 'n' or what != rule.yields:
                            continue
                        item = _add(chart[i], orule, odot + 1, oorigin,
                                    (*oparts, made))
                        if item is not None:
                            queue.append(item)
                    continue
                kind, what = rule.symbols[dot]
                if kind == 'n':
                    if (i, what) not in told:
                        told.add((i, what))
                        for other in self.by_yield[what]:
                            item = _add(chart[i], other, 0, i, ())
                            if item is not None:
                                queue.append(item)
                    # A variable of the statement stands for itself.
                    if i < n and self.typecode.get(tokens[i]) == what:
                        _add(chart[i + 1], rule, dot + 1, origin,
                             (*parts, Term(variable=tokens[i])))
                elif i < n and tokens[i] == what:
                    _add(chart[i + 1], rule, dot + 1, origin, parts)

        found = [self.build(r, p) for r, d, o, p in chart[n].values()
                 if o == 0 and d == len(r.symbols) and r.yields == start]
        if not found:
            raise Problem('', 0, f'cannot read {" ".join(tokens)!r}')
        return found[0]

    def statement(self, signature):
        """A labelled statement's claim, as a term."""
        return self.parse(signature.statement[1:], 'wff')


def _add(row, rule, dot, origin, parts):
    """Put one item in a chart row, and give it back if it is new.

    A `Rule` is hashed by identity, so it keys the row as it stands. The
    caller wants the item it just added and not a second lookup for it:
    this runs a hundred million times in a corpus build, and the row is
    the hottest dictionary in the program."""
    key = (rule, dot, origin)
    if key in row:
        return None
    item = row[key] = (rule, dot, origin, parts)
    return item
