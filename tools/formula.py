"""Parse a formula from the notations declared in db/notation.db.

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


def tokenise(text, words, symbols):
    """A run of letters is a declared word if one matches by longest match, and
    otherwise a single name. A numeral is a maximal run of digits. Round
    brackets belong to the grammar rather than to any notation.

    At the start of a sentence a declared word also matches with its first
    letter capitalised, which is how the corpus writes `For every` and
    `There is`. The allowance is deliberately that narrow: matching case
    anywhere would let the name `s` match the declared word `S`."""
    out, i = [], 0
    while i < len(text):
        m = SPACE.match(text, i)
        if m:
            i = m.end()
            continue
        if text[i] == '(':
            out.append(Token('open', '(', i)); i += 1; continue
        if text[i] == ')':
            out.append(Token('close', ')', i)); i += 1; continue
        m = DIGITS.match(text, i)
        if m:
            out.append(Token('numeral', m.group(), i)); i = m.end(); continue
        m = LETTERS.match(text, i)
        if m:
            run = m.group()
            candidates = [run]
            if not out and run[:1].isupper():
                candidates.append(run[0].lower() + run[1:])
            hit = next((w for c in candidates
                        for n in range(len(c), 0, -1)
                        for w in [c[:n]] if w in words), None)
            if hit:
                out.append(Token('word', hit, i)); i += len(hit); continue
            m = NAME.match(text, i)
            out.append(Token('name', m.group(), i)); i = m.end(); continue
        sym = next((s for s in symbols if text.startswith(s, i)), None)
        if sym:
            out.append(Token('symbol', sym, i)); i += len(sym); continue
        raise Problem('', 0, f'no token at {text[i:i+12]!r} in {text!r}')
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
        for n, pat in enumerate(re.split(r'\s{2,}', raw)):
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
            out.append(Notation(
                name=r.name, parts=parts, holes=holes,
                yields=r.fields.get('yields', '').strip(),
                level=(levels[n] if n < len(levels) else levels[0]).strip(),
                assoc=(assocs[n] if n < len(assocs) else assocs[0]).strip() or None,
                binds=r.fields.get('binds')))
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
        compared by. Layout plays no part once the tree is built."""
        if not self.children:
            return f'{self.notation}:{self.text}'
        inner = ', '.join(c.shape() for c in self.children)
        return f'{self.notation}({inner})'
