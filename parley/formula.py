"""Parse a formula from the notations declared in db/notation.records.

GRAMMAR.md's "Formulas" section is the specification. Nothing here knows any
notation by name: the patterns, their hole sorts, their precedence levels and
their associativity all come from the database, so adding a notation is a
database entry and never a change to this file.
"""
import re
from dataclasses import dataclass, field

from parse import Problem

# ------------------------------------------------------------------ tokens

NAME = re.compile(r'[A-Za-zα-ωΑ-Ω][₀-₉′]*')
DIGITS = re.compile(r'\d+')
LETTERS = re.compile(r'[A-Za-zα-ωΑ-Ω]+')
SPACE = re.compile(r'\s+')


@dataclass
class Token:
    kind: str          # 'word', 'name', 'numeral', 'symbol', 'open', 'close'
    text: str
    at: int


def tokenise(text, words, symbols, path='', line=0):
    """A run of letters is a declared word if one matches by longest match, and
    otherwise a single name. A numeral is a maximal run of digits. Round
    brackets belong to the grammar rather than to any notation.

    The position is carried because text that does not lex is a defect with
    somewhere to point, and a defect with nowhere to point reads like a
    route declining.

    At the start of a sentence a declared word also matches with its first
    letter capitalised, which is how the corpus writes `For every` and
    `There is`. The allowance is deliberately that narrow: matching case
    anywhere would let the name `s` match the declared word `S`."""
    out, i = [], 0

    def take(kind, spelling, at):
        out.append(Token(kind, spelling, at))
        return at + len(spelling)

    while i < len(text):
        m = SPACE.match(text, i)
        if m:
            i = m.end()
            continue
        if text[i] in '()':
            i = take('open' if text[i] == '(' else 'close', text[i], i)
            continue
        m = DIGITS.match(text, i)
        if m:
            i = take('numeral', m.group(), i)
            continue
        m = LETTERS.match(text, i)
        if m:
            run = m.group()
            candidates = [run]
            if not out and run[:1].isupper():
                candidates.append(run[0].lower() + run[1:])
            # Only a word of two letters or more is lexed as a word. Three
            # declared literals are a single letter, `a` in "form a triangle"
            # and in "there is a bijection", and `S` and `G` naming the two
            # sum functions. All three are also variable names in the corpus,
            # and `a` is one of the commonest. A single letter is therefore
            # always a name, and a pattern's single-letter literal still
            # matches it, because a pattern matches a token by its text.
            hit = next((w for c in candidates
                        for n in range(len(c), 1, -1)
                        for w in [c[:n]] if w in words), None)
            if hit:
                i = take('word', hit, i)
                continue
            i = take('name', NAME.match(text, i).group(), i)
            continue
        sym = next((s for s in symbols if text.startswith(s, i)), None)
        if sym:
            i = take('symbol', sym, i)
            continue
        raise Problem(path, line,
                      f'no token at {text[i:i+12]!r} in {text!r}')
    return out


# ------------------------------------------------------- notation as data

@dataclass
class Notation:
    name: str
    parts: list            # tokens and the marker HOLE, in order
    holes: list            # the declared sort of each hole
    yields: str
    level: str
    assoc: str = None
    binds: str = None
    folds: str = None          # the notation this pattern is the negation under
    literal: str = ''          # the tokens the node it builds stands for
    stands_under: str = ''     # the record's name, or another it spells
    fold_literal: str = ''     # the literal of the notation that wraps it


NEGATES = re.compile(r'pattern\s+(\d+)\s+is\s+(\S+)\s+of\s+pattern\s+(\d+)')
SPELLS = re.compile(r'^\s*(\S+)\s+(\S+)')


HOLE = object()


def compile_notations(records):
    """Turn notation records into patterns the parser can match."""
    out, words, symbols = [], set(), set()
    for r in records:
        if r.kind != 'notation':
            continue
        raw = r.fields.get('pattern', '').strip()
        if not raw:
            continue
        holes = [h.strip() for h in r.fields.get('holes', '').split(',') if h.strip()]
        if holes == ['none']:
            holes = []
        levels = [x.strip() for x in r.fields.get('level', '').split(',')]
        assocs = [x.strip() for x in r.fields.get('assoc', '').split(',')]
        # A record may declare that one of its patterns is the negation of
        # another. Both then build the same tree, so "n is not odd" and
        # "not (n is odd)" are one formula wherever two are compared.
        folded = NEGATES.search(r.fields.get('negates', ''))
        spells = SPELLS.search(r.fields.get('spells', ''))
        shapes = []
        for pat in re.split(r'\s{2,}', raw):
            parts = []
            for piece in re.findall(r'_|[^_\s]+', pat):
                if piece == '_':
                    parts.append(HOLE)
                    continue
                # A literal may run a word straight into a symbol, as `gcd(`
                # does. Split it, or the word is never declared and every use
                # of it falls back to single letters.
                for bit in re.findall(r'[A-Za-zα-ωΑ-Ω]+|[^A-Za-zα-ωΑ-Ω]', piece):
                    parts.append(bit)
                    if LETTERS.fullmatch(bit):
                        words.add(bit)
                    elif bit not in '()':
                        symbols.add(bit)
            shapes.append(parts)
        # What a node is called and what stands in it: a record's name and the
        # literal of the pattern that matched. Both are needed, or `a < b` and
        # `a ≥ b` are one tree, since they are patterns of one record.
        #
        # A pattern that spells another builds the other's node, which is how
        # `2r` and `2·r` come out the same, and a pattern declared as the
        # negation of another carries that one's literal, so that the wrapping
        # in `not` is the only difference between the two spellings.
        for n, parts in enumerate(shapes):
            stands = ''.join(p for p in parts if p is not HOLE)
            under = r.name
            if folded and int(folded.group(1)) == n + 1:
                base = shapes[int(folded.group(3)) - 1]
                stands = ''.join(p for p in base if p is not HOLE)
            elif spells:
                under, stands = spells.group(1), spells.group(2)
            out.append(Notation(
                literal=stands, stands_under=under,
                name=r.name, parts=parts, holes=holes,
                yields=r.fields.get('yields', '').strip(),
                level=(levels[n] if n < len(levels) else levels[0]).strip(),
                assoc=(assocs[n] if n < len(assocs) else assocs[0]).strip() or None,
                binds=r.fields.get('binds'),
                folds=(folded.group(2) if folded
                       and int(folded.group(1)) == n + 1 else None)))
    # A folded pattern builds the notation that wraps it, so it needs that
    # notation's literal too: `n is not odd` has to come out the same as
    # `not (n is odd)`, down to what stands in the outer node.
    literals = {}
    for n in out:
        literals.setdefault(n.stands_under or n.name, n.literal)
    for n in out:
        if n.folds:
            n.fold_literal = literals.get(n.folds, '')
    # A symbol may be a prefix of another, so try the longest first.
    return out, words, sorted(symbols, key=len, reverse=True)


def compile_precedence(records):
    """The partial order. `tighter[a]` is everything a binds more tightly than,
    closed under transitivity. Levels unrelated in either direction are
    incomparable and an expression mixing them needs brackets."""
    direct = {}
    for r in records:
        if r.kind != 'precedence':
            continue
        for key, value in r.fields.items():
            if key == 'note':
                continue
            m = re.match(r'tighter than\s+(.*)', value.strip())
            if m:
                direct[key] = [x.strip().rstrip('.') for x in m.group(1).split(',')]
    tighter = {}
    for start in direct:
        seen, stack = set(), list(direct.get(start, []))
        while stack:
            lv = stack.pop()
            if lv in seen:
                continue
            seen.add(lv)
            stack += direct.get(lv, [])
        tighter[start] = seen
    return tighter


def binds_tighter(tighter, a, b):
    """True when a nests inside b. None when the two are incomparable."""
    if a == b:
        return None
    if b in tighter.get(a, ()):
        return True
    if a in tighter.get(b, ()):
        return False
    return None


# ------------------------------------------------------------------ parse

@dataclass
class Node:
    notation: str
    sort: str
    children: list = field(default_factory=list)
    text: str = ''

    def shape(self):
        """A parenthesis-free rendering, which is what two instances are
        compared by. Layout plays no part once the tree is built.

        The literal is part of it wherever there is one, because a record may
        declare several patterns and they are different formulas: `a < b` and
        `a ≥ b` are both `order`, and only the sign tells them apart."""
        head = f'{self.notation}:{self.text}' if self.text else self.notation
        if not self.children:
            return head
        inner = ', '.join(c.shape() for c in self.children)
        return f'{head}({inner})'

    def names(self):
        if not self.children:
            return {self.text} if self.notation == 'name' else set()
        return set().union(*(c.names() for c in self.children)) or set()


class Ambiguous(Problem):
    """Two notations fit and the sorts do not separate them. The parser says
    so rather than choosing, because choosing is how a reader and the kernel
    come to hold different formulas without anything noticing."""


@dataclass
class Grammar:
    notations: list
    words: set
    symbols: list
    tighter: dict
    sorts: dict = field(default_factory=dict)   # name -> sort, from the proof

    @classmethod
    def load(cls, records):
        nots, words, symbols = compile_notations(records)
        return cls(nots, words, symbols, compile_precedence(records))


def fits(hole, sort):
    """A value fits a hole when the sorts agree, when the hole takes any term,
    or when the value's sort is not known. The last is the permissive rule: a
    value of no known sort fits anywhere, because refusing it would reject
    proofs for failing a test the sorts were never introduced to run.

    `any` means two different things and both are unknown-ish. As a hole it
    says "any term"; as what a notation yields, as application does, it says
    "whatever came back", which is exactly a value of no known sort."""
    if sort in (None, 'unknown', 'any'):
        return True
    if hole == 'any':
        return sort in TERM_SORTS
    return hole == sort


TERM_SORTS = {'number', 'set', 'point', 'any'}


def parse(text, g, path='', line=0):
    """Parse one sentence. Returns a Node, or raises Problem.

    Nothing below raises for a reading that did not work out: it gives back
    None and says where it stopped. This is the one place that turns having
    no reading into a defect, because it is the one place that knows there
    is no other reading left to try."""
    tokens = tokenise(text, g.words, g.symbols, path, line)
    p = _Parser(tokens, g, path, line, text)
    node = p.expression(None)
    if node is None:
        raise Problem(path, line, p.why())
    if p.i != len(tokens):
        raise Problem(path, line,
                      f'{text!r} has {len(tokens) - p.i} token(s) left over, '
                      f'starting at {tokens[p.i].text!r}')
    return node


class _Parser:
    """One sentence being read.

    A notation is recognised by trying it, so most of what is tried does not
    fit and saying so is not a complaint: `p` in `d divides p, and ...` is a
    candidate first point of a triangle until the comma rules it out, and a
    sentence of ordinary words rules out dozens. So not fitting is a value
    here and never an exception. `Ambiguous` is the exception, because two
    notations fitting is a defect however it was reached.

    What is lost by returning rather than raising is the message, since only
    the last reading to fail used to leave one. `stopped` keeps the furthest
    any reading reached and what stood in its way there, which is the
    reading that got closest to working and the one worth telling a reader
    about."""

    def __init__(self, tokens, g, path, line, text):
        self.t, self.g, self.path, self.line, self.src = tokens, g, path, line, text
        self.i = 0
        self.stopped = (-1, '')

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def no(self, message):
        """No reading here, and why. Always None, so a caller may `return
        self.no(...)` and be read as giving up rather than as reporting."""
        if self.i > self.stopped[0]:
            self.stopped = (self.i, message)
        return None

    def why(self):
        """What to say about a sentence no reading fitted."""
        return self.stopped[1] or f'nothing reads {self.src!r}'

    def expression(self, outer, stop=None):
        """Parse a primary, then extend it with any notation whose first hole
        it can fill, so long as that notation binds tighter than `outer`.

        `stop` is the literal that closes an interior hole. Without it the hole
        runs past its own delimiter: the set in `for every s ∈ S, d ≤ s` would
        swallow the comma and try to be the first point of a triangle."""
        left = self.primary()
        if left is None:
            return None
        while True:
            nxt = self.peek()
            if stop is not None and nxt is not None and nxt.text == stop:
                return left
            nxt = self.extend(left, outer)
            if nxt is None:
                return left
            left = nxt

    def primary(self):
        tok = self.peek()
        if tok is None:
            return self.no(f'{self.src!r} ends early')
        if tok.kind == 'open':
            self.i += 1
            inner = self.expression(None)
            if inner is None:
                return None
            if not self.peek() or self.peek().kind != 'close':
                return self.no(f'unclosed bracket in {self.src!r}')
            self.i += 1
            return inner
        # A notation may open with a literal that is also a name, as the two
        # sum functions do with S and G. Try those as well as the bare name and
        # take whichever reaches further.
        cands = [n for n in self.g.notations
                 if n.parts and n.parts[0] is not HOLE and n.parts[0] == tok.text]
        if tok.kind in ('name', 'numeral'):
            leaf = (Node('name', self.g.sorts.get(tok.text, 'unknown'), text=tok.text)
                    if tok.kind == 'name' else Node('numeral', 'number', text=tok.text))
            if not cands:
                self.i += 1
                return leaf
            found = self.apply(cands, None)
            if found is not None:
                return found
            self.i += 1
            return leaf
        return self.apply(cands, None)

    def extend(self, left, outer):
        """Notations whose pattern opens with a hole, which `left` fills."""
        tok = self.peek()
        if tok is None or tok.kind == 'close':
            return None
        cands = []
        for n in self.g.notations:
            if not n.parts or n.parts[0] is not HOLE or len(n.parts) < 2:
                continue
            # A pattern whose second part is also a hole has no token to
            # recognise it by: juxtaposition. It is a candidate whenever what
            # follows could begin a term.
            if n.parts[1] is HOLE:
                if tok.kind not in ('name', 'numeral', 'open'):
                    continue
                # Juxtaposition never joins two bare names. That restriction is
                # what makes a run of letters decidable at all, since `and`
                # would otherwise read as a product of three variables the
                # corpus uses. It leaves `2k` and `k(k + 1)`, which are the
                # only shapes the corpus writes.
                if tok.kind == 'name' and left.notation == 'name':
                    continue
            elif n.parts[1] != tok.text:
                continue
            if not fits(n.holes[0], left.sort):
                continue
            # A pattern that ends in a token and declares no level is closed:
            # it competes for nothing that follows and nests anywhere, as
            # `f(x)` and `|x|` do. A pattern that declares a level takes part
            # in precedence wherever it stands, even when a token closes it,
            # or `√2 is irrational` reads as the root of `2 is irrational`.
            if outer is not None and (n.parts[-1] is HOLE or n.level):
                tight = binds_tighter(self.g.tighter, n.level, outer)
                if tight is not True:
                    continue
            cands.append(n)
        if not cands:
            return None
        # An extension is optional, so a candidate that cannot match ends the
        # expression rather than failing it. The sorts only narrow the
        # candidates and a value of unknown sort fits every hole, so a pattern
        # is regularly reached here that the tokens then rule out: `p` in
        # `d divides p, and ...` is a candidate first point of a triangle, and
        # without this the comma would fail the sentence it merely ends a
        # clause of.
        return self.apply(cands, left)

    def apply(self, cands, left):
        """Try each candidate. Exactly one must fit, or none does and this
        is no reading; two do and the text is ambiguous, which is a defect
        and the one thing here that is raised."""
        if not cands:
            tok = self.peek()
            return self.no(f'no notation starts at {tok.text!r} '
                           f'in {self.src!r}')
        start, results = self.i, []
        for n in cands:
            self.i = start
            found = self.match(n, left)
            if found is not None:
                results.append((found, self.i))
        if not results:
            self.i = start
            tok = self.peek()
            return self.no(f'no notation fits at {tok.text!r} '
                           f'in {self.src!r}')
        best = max(r[1] for r in results)
        winners = [r for r in results if r[1] == best]
        if len(winners) > 1:
            names = ', '.join(sorted({w[0].notation for w in winners}))
            raise Ambiguous(self.path, self.line,
                            f'{self.src!r} fits {names} and the sorts do not '
                            f'separate them')
        self.i = winners[0][1]
        return winners[0][0]

    def match(self, n, left):
        """Match one pattern, filling its holes.

        A hole with a token after it is delimited by that token and takes any
        expression. Only a hole at the right edge needs the pattern's level as
        a barrier, since only there can a looser notation swallow the rest."""
        kids = []
        for k, part in enumerate(n.parts):
            if part is HOLE:
                want = n.holes[len(kids)] if len(kids) < len(n.holes) else 'any'
                if k == 0 and left is not None:
                    kids.append(left)
                else:
                    at_edge = k == len(n.parts) - 1
                    after = n.parts[k + 1] if not at_edge else None
                    kid = self.hole(want, n.level if at_edge else None,
                                    after if after is not HOLE else None)
                    if kid is None:
                        return None
                    kids.append(kid)
                continue
            tok = self.peek()
            if tok is None or tok.text != part:
                return self.no(f'{n.name} does not fit at '
                               f'{tok.text!r} in {self.src!r}'
                               if tok is not None else
                               f'{self.src!r} ends early')
            self.i += 1
        # A pattern may name fewer hole sorts than it has holes, which the
        # record check reports; here the extra holes simply go unchecked.
        for kid, want in zip(kids, n.holes, strict=False):
            if not fits(want, kid.sort):
                return self.no(f'{n.name} wants {want} and got {kid.sort}')
        # The node is named by the record and carries the literal of the
        # pattern it stands for. Both are needed: ℝ and ℕ₀ are one record, and
        # so are `a < b` and `a ≥ b`, and nothing comparing two formulas could
        # otherwise tell either pair apart.
        node = Node(n.stands_under or n.name, n.yields, kids, n.literal)
        # A pattern declared as the negation of another builds the other and
        # wraps it, so the folded spelling and the `not` spelling are one tree.
        # The wrapper is named by the record, not known here.
        if n.folds is None:
            return node
        return Node(n.folds, 'formula', [node], n.fold_literal)

    def hole(self, want, barrier, stop):
        """A `variable` hole takes a bare name; any other takes an expression,
        bounded by `barrier` when the hole sits at the pattern's right edge and
        by `stop`, the literal that follows it, when it does not."""
        if want == 'variable':
            tok = self.peek()
            if tok is None or tok.kind != 'name':
                return self.no('a binder wants a name')
            self.i += 1
            return Node('name', 'variable', text=tok.text)
        return self.expression(barrier, stop)
