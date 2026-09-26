"""Kinds: what a set holds, read off how a text uses its names.

`READERS.md` says a set has the kind of what it holds and the page never
writes it, and `GRAMMAR.md` says how it is read: each notation's `kinds`
field in `db/notation.records` relates the kinds of its holes, and a name
takes the most general kind the text allows. This module is that reading:
kind terms, the one field's syntax, unification, and inference over a parse
tree. The checker decides what to read and reports what does not fit.

A kind is `number`, `point`, `formula`, `set of K`, `property of K`,
`function from K to K`, or a variable. A variable is *flexible* when the text
may still say what it is, and *rigid* when it stands for "any kind" a
statement declared — `let X be a set` makes X a set of a rigid kind, which
its own statement and proof may not narrow, since the statement is claimed
of every kind. A cited statement's kinds are copied flexible at each use, so
each citing step takes the kind it needs.

Unifying two kinds that do not fit gives back a `Declined` saying why. That
is a value and not an exception: the checker reports it, and nothing tries
another reading after it.
"""
import itertools
import re

from formula import parse
from match import Rule
from parse import Declined, Problem, declined, define_parts
from sorts import LABEL, SENTENCE, element_sort, file_definitions

OBTAINS = re.compile(r'^obtain\s+([^:]+?)(?::|\s+from)')

_ids = itertools.count()

# The kinds a thing can be that are not sets of something.
NUMBER, POINT, FORMULA = ('number',), ('point',), ('formula',)


class Var:
    """A kind not yet known (flexible), or one declared any (rigid)."""
    __slots__ = ('id', 'ref', 'rigid', 'said')

    def __init__(self, rigid=False, said=''):
        self.id, self.ref, self.rigid, self.said = next(_ids), None, rigid, said


def find(k):
    while isinstance(k, Var) and k.ref is not None:
        k = k.ref
    return k


def show(k):
    """A kind as a reader would say it."""
    k = find(k)
    if isinstance(k, Var):
        return f'any kind{f" ({k.said})" if k.said else ""}' if k.rigid \
            else 'a kind not yet fixed'
    if k[0] in ('number', 'point', 'formula'):
        return {'number': 'a number', 'point': 'a point',
                'formula': 'a statement'}[k[0]]
    if k[0] == 'set':
        return f'a set of {_plural(k[1])}'
    if k[0] == 'property':
        return f'a property of {_plural(k[1])}'
    return f'a function from {_plural(k[1])} to {_plural(k[2])}'


def _plural(k):
    said = show(k)
    for one, many in (('a number', 'numbers'), ('a point', 'points'),
                      ('a statement', 'statements'), ('a set of', 'sets of'),
                      ('a property of', 'properties of'),
                      ('a function from', 'functions from')):
        if said.startswith(one):
            return many + said[len(one):]
    return 'things of ' + said


def _occurs(v, k):
    k = find(k)
    if k is v:
        return True
    return isinstance(k, tuple) and any(_occurs(v, c) for c in k[1:])


def unify(a, b):
    """None where the two kinds can be one, else a `Declined` saying why."""
    a, b = find(a), find(b)
    if a is b:
        return None
    if isinstance(a, Var) and not a.rigid:
        if _occurs(a, b):
            return Declined(f'{show(b)} would have to hold itself')
        a.ref = b
        return None
    if isinstance(b, Var) and not b.rigid:
        return unify(b, a)
    if isinstance(a, Var) or isinstance(b, Var):
        rigid, other = (a, b) if isinstance(a, Var) else (b, a)
        return Declined(f'{show(rigid)} is declared of any kind, and here it '
                        f'would have to be {show(other)}')
    if a[0] != b[0] or len(a) != len(b):
        return Declined(f'{show(a)} where {show(b)} is wanted')
    for x, y in zip(a[1:], b[1:], strict=True):
        said = unify(x, y)
        if declined(said):
            return Declined(f'{show(a)} where {show(b)} is wanted')
    return None


# ------------------------------------------------------------ the field

_TOKEN = re.compile(r'set of|property of|function from|to|number|point|'
                    r'formula|[α-ω]')


def signature(text):
    """A `kinds` field, as a maker of fresh (hole kinds, result kind).

    Or a `Declined` saying what in the field does not read. `check_notation`
    reports that; everything else skips a notation whose field is one.
    """
    holes_text, arrow, result_text = text.partition('→')
    if not arrow:
        return Declined(f'{text!r} has no `→` before what it produces')
    holes = [h.strip() for h in holes_text.split(',') if h.strip()]
    templates = [_read(h) for h in holes] + [_read(result_text.strip())]
    for one in templates:
        if declined(one):
            return one
    *parts, result = templates

    def fresh():
        names = {}
        return ([_instance(t, names) for t in parts],
                _instance(result, names))
    fresh.holes = len(parts)
    return fresh


def _read(text):
    tokens = _TOKEN.findall(text)
    if ''.join(tokens).replace(' ', '') != text.replace(' ', ''):
        return Declined(f'{text!r} is not a kind')
    got = _term(tokens)
    if declined(got):
        return got
    tree, rest = got
    if rest:
        return Declined(f'{text!r} has {" ".join(rest)!r} left over')
    return tree


def _term(tokens):
    if not tokens:
        return Declined('a kind is missing')
    head, rest = tokens[0], tokens[1:]
    if head in ('number', 'point', 'formula'):
        return (head,), rest
    if head in ('set of', 'property of'):
        got = _term(rest)
        if declined(got):
            return got
        inner, rest = got
        return (head.split()[0], inner), rest
    if head == 'function from':
        got = _term(rest)
        if declined(got):
            return got
        a, rest = got
        if not rest or rest[0] != 'to':
            return Declined('`function from` wants `to`')
        got = _term(rest[1:])
        if declined(got):
            return got
        b, rest = got
        return ('function', a, b), rest
    if head == 'to':
        return Declined('`to` stands without `function from`')
    return ('var', head), rest


def _instance(t, names):
    if t[0] == 'var':
        return names.setdefault(t[1], Var())
    return (t[0], *(_instance(c, names) for c in t[1:]))


def copy(k, seen):
    """A kind with its variables replaced by fresh flexible ones.

    The same fresh one stands wherever the same variable stood, so what a
    cited statement relates stays related in the copy.
    """
    k = find(k)
    if isinstance(k, Var):
        if k.id not in seen:
            seen[k.id] = Var()
        return seen[k.id]
    return (k[0], *(copy(c, seen) for c in k[1:]))


# ------------------------------------------------------------ reading

class Reader:
    """Kinds over one statement or proof, read in the order it is written.

    `env` maps a name to its kind; a `let` shadows what came before, since a
    block may use a letter an earlier one did. What does not fit is kept in
    `clashes` as (line, what, why).
    """

    def __init__(self, grammar):
        self.g = grammar
        self.env, self.clashes = {}, []
        self.declared = []       # names declared of any kind, not yet fixed
        self.signatures, self.bound = {}, {}
        for n in grammar.notations:
            key = n.stands_under or n.name
            made = signature(n.kinds) if n.kinds else None
            if made is None or declined(made):
                continue
            self.signatures.setdefault(key, made)
            self.signatures.setdefault(n.name, made)
            if n.holes:
                self.bound.setdefault(key, set()).update(
                    i for i, h in enumerate(n.holes) if h == 'variable')

    def of_name(self, name):
        if name not in self.env:
            self.env[name] = Var()
        return self.env[name]

    def kind(self, node, line, local=None):
        """The kind of a parse tree, noting every clash inside it."""
        local = local or {}
        if node.notation == 'name':
            return local.get(node.text) or self.of_name(node.text)
        if node.notation == 'numeral':
            return NUMBER
        make = self.signatures.get(node.notation)
        if make is None or make.holes != len(node.children):
            holes, out = self._by_sort(node)
        else:
            holes, out = make()
        inner = dict(local)
        for i in self.bound.get(node.notation, ()):
            if i < len(node.children) \
                    and node.children[i].notation == 'name':
                inner[node.children[i].text] = Var()
        for child, want in zip(node.children, holes, strict=True):
            got = self.kind(child, line, inner)
            said = unify(got, want)
            if declined(said):
                what = child.text or child.notation
                self.clashes.append((line, what, str(said)))
        return out

    @staticmethod
    def _by_sort(node):
        by = {'number': lambda: NUMBER, 'point': lambda: POINT,
              'formula': lambda: FORMULA, 'set': lambda: ('set', Var())}
        return ([by.get(c.sort, Var)() for c in node.children],
                by.get(node.sort, Var)())

    def claim(self, node, line):
        said = unify(self.kind(node, line), FORMULA)
        if declined(said):
            self.clashes.append((line, 'the line', str(said)))

    def fix_declared(self):
        """Make what the declared names' kinds still leave open rigid.

        Called once the lines declaring them are read: the statement's
        hypotheses and conclusion, or a block's opening lines. What they
        related is related; what they left open is "any kind" from here on,
        and a proof that narrows it is proving less than it claims.
        """
        for name in self.declared:
            _rigid(self.env.get(name), name)
        self.declared = []


def _rigid(k, name):
    k = find(k)
    if isinstance(k, Var):
        k.rigid, k.said = True, k.said or name
    elif isinstance(k, tuple):
        for c in k[1:]:
            _rigid(c, name)


def sort_of(k):
    """The flat sort a kind settles, or None where it settles none."""
    k = find(k)
    if isinstance(k, Var):
        return None
    return {'number': 'number', 'point': 'point', 'set': 'set',
            'function': 'function', 'property': 'property'}.get(k[0])


# ------------------------------------------------------------ a text

def introduce(reader, body, line, g):
    """What a `let` line says a name is, into `reader`'s kinds.

    `be a set` and `be an element` declare a thing of any kind. The lines
    declaring it may still relate it to another — `X ∖ {a}` makes a the kind
    of what X holds — so the kind is left free here and noted in `declared`,
    and `fix_declared` fixes it once the statement or the block's opening
    lines are read. The rest name a thing whose kind the text fixes, and the
    line is read as a claim.
    """
    body = LABEL.sub('', body).strip()
    m = re.match(r'^(\S+)\s+be a set$', body)
    if m:
        reader.env[m.group(1)] = ('set', Var(said=m.group(1)))
        reader.declared.append(m.group(1))
        return
    m = re.match(r'^(\S+)\s+be an element$', body)
    if m:
        reader.env[m.group(1)] = Var(said=m.group(1))
        reader.declared.append(m.group(1))
        return
    m = re.match(r'^(\S+)\s+be a point$', body)
    if m:
        reader.env[m.group(1)] = POINT
        return
    m = re.match(r'^(\S+)\s+be a property of the elements of\s+(\S+)$', body)
    if m:
        of = Var()
        reader.env[m.group(1)] = ('property', of)
        said = unify(reader.of_name(m.group(2)), ('set', of))
        if declined(said):
            reader.clashes.append((line, m.group(2), str(said)))
        return
    m = re.match(r'^([^\s∈∉:]+)\s*(?:∈|∉|:)', body)
    if m:
        reader.env[m.group(1)] = Var()
    claim_text(reader, body, line, g)


def claim_text(reader, text, line, g):
    """Every sentence of a line, read as a claim.

    One that does not parse is `check_formulas`'s to report, and is passed
    over here.
    """
    for sentence in SENTENCE.split(text.strip()):
        sentence = sentence.strip().rstrip('.').strip()
        if not sentence:
            continue
        try:
            node = parse(sentence, g)
        except Problem:
            continue
        reader.claim(node, line)


def read_record(record, g):
    """An item's kinds, read from its own lines in the order they are written.

    A record keeps the keyword of a hypothesis in the field name where a
    proof line keeps it in the text, and has no steps. The parser's sorts
    for `record` must be in `g` already.
    """
    reader = Reader(g)
    for kind, text, _label, no in record.hypotheses:
        if kind == 'let':
            introduce(reader, text, no, g)
        else:
            claim_text(reader, LABEL.sub('', text).strip(), no, g)
    for text, no in record.conclusions:
        claim_text(reader, text, no, g)
    return reader


def read_theorem(thm, g, cite=None):
    """A theorem's kinds, read in the order its lines are written.

    A `let` shadows an earlier name, since blocks reuse letters. What the
    statement or a block's opening lines declared of any kind is fixed where
    the proof under them begins. `cite(reader, step)` is called after each
    step's claim is read, for whoever fits its citations. The parser's sorts
    for `thm` must be in `g` already.
    """
    reader = Reader(g)
    # What the theorem sees from outside it has its kind before its first
    # line, read from the rule written out where it was defined.
    for name, made in file_definitions(thm, g).items():
        if isinstance(made, Rule):
            taken = Var()
            reader.env[name] = ('function', taken,
                                reader.kind(made.body, thm.line,
                                            {made.param: taken}))
        else:
            reader.env[name] = reader.kind(made, thm.line)
    events = [(no, kind, text[len(kind):], None)
              for kind, text, _label, no in thm.hypotheses]
    # The conclusion is the statement's last line, so it may still relate
    # what the hypotheses declared of any kind.
    after = max((no for _k, _t, _l, no in thm.hypotheses), default=thm.line)
    events.append((after + 0.5, 'conclusion', thm.conclusion, None))
    events += [(no, 'define', text, None) for _k, text, _l, no in thm.defines]
    for step in thm.steps:
        events += [(no, kind, text[len(kind):], None)
                   for kind, text, _label, no, _p in step.openers]
        events.append((step.line, 'claim', ' '.join(step.claim), step))
        events += [(no, 'requires', fact, None)
                   for fact, _how, no in step.requires]
    for no, kind, text, step in sorted(events, key=lambda e: e[0]):
        if kind in ('define', 'claim', 'requires'):
            reader.fix_declared()
        if kind == 'let':
            introduce(reader, text, no, g)
        elif kind == 'define':
            said = define_parts(text)
            if declined(said):
                continue
            if said.param is None:
                try:
                    reader.env[said.name] = reader.kind(parse(said.body, g),
                                                        no)
                except Problem:
                    continue
                continue
            # A function: what its domain holds goes in, what its rule gives
            # comes out, and the parameter is its rule's own name.
            kept = g.sorts
            g.sorts = {**kept, said.param: element_sort(said.domain)}
            try:
                over = reader.kind(parse(said.domain, g), no)
                taken = Var()
                said_of = unify(over, ('set', taken))
                if declined(said_of):
                    reader.clashes.append((no, said.domain, str(said_of)))
                gives = reader.kind(parse(said.body, g), no,
                                    {said.param: taken})
                reader.env[said.name] = ('function', taken, gives)
            except Problem:
                continue
            finally:
                g.sorts = kept
        elif kind == 'claim':
            obtained = OBTAINS.match(step.just.text) \
                if step.just and step.just.head == 'obtain' else None
            if obtained:
                for name in re.split(r'\s*,\s*', obtained.group(1).strip()):
                    reader.env[name] = Var()
            claim_text(reader, text, no, g)
            if cite is not None:
                cite(reader, step)
        else:
            claim_text(reader, LABEL.sub('', text).strip(), no, g)
    return reader
