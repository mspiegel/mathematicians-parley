"""Writing Metamath from Python, in the two ways this project writes it.

A Metamath statement is a flat run of tokens and a proof is a flat run of
labels in reverse Polish. Neither is comfortable to type, so everything here
that produces one goes through this module.

There are two ways, and the difference is who does the transcription.

The constructors below build reverse Polish directly: `mul(a, b)` is the
product of two terms already in reverse Polish. They are what the five
hand-written proofs in `elaboration/` use, and they need nothing but
themselves — no set.mm, no parser.

`Builder` goes the other way. A statement is written once, in the notation
set.mm writes it in, and `rpn` parses it; `ap` assembles one proof step from a
label and what it is applied to, reading the push order off the label's own
signature. Nothing is transcribed into stack order by hand. It needs the
library, because only the library knows what a label wants pushed.

The second is the better of the two and the first is not deprecated: a script
with no other reason to read set.mm would gain a 51 MB dependency by moving.
"""
from dataclasses import dataclass

import kernel
from library import Signature


@dataclass(frozen=True)
class Proof:
    """A proof, and what on the page it rests on.

    `origin` names the things a reader can point at — a hypothesis, a block's
    assumption, a proved line, a `requires` line — that went into this proof.
    Library labels are not among them: they are what the page never writes.
    `GOALS.md` decision 9 is that the kernel proof is derived from the text,
    and this is what lets that be asked of a proof rather than assumed.

    It is not text: `.text` is what it spells. Code that handled a proof as
    a string and so lost what it rests on would leave a proof resting on
    nothing, which every check of what a step names would pass. So `str`
    and a format refuse, the way `seq` refuses a decline, and the line that
    forgot is the line that fails.
    """

    text: str
    origin: frozenset = frozenset()

    def __post_init__(self):
        if not isinstance(self.text, str):
            raise TypeError(f'a proof is text, not {type(self.text).__name__}')
        object.__setattr__(self, 'origin', frozenset(self.origin))

    def __str__(self):
        raise TypeError('a proof is not text; .text is what it spells')

    def __format__(self, spec):
        raise TypeError('a proof is not text; .text is what it spells')


def seq(*parts):
    """Tokens in order, skipping any that are empty, as text.

    This builds terms and formulas, and whatever a script without a library
    writes. A proof is built by `Builder.seq`, which knows the labels and so
    can tell one from the other; a proof handed here is refused, since the
    text this gives back would carry nothing of what the proof rests on.
    Anything else that is not text — a decline — is refused by the join.
    """
    for p in parts:
        if type(p) is Proof:
            raise TypeError('a proof joined as text; Builder.seq builds one')
    return ' '.join(p for p in parts if p)


# Terms. `co` is Metamath's binary operation and most of the rest are it with
# the operator filled in.
def co(a, b, f):
    return seq(a, b, f, 'co')


def mul(a, b):
    return co(a, b, 'cmul')


def add(a, b):
    return co(a, b, 'caddc')


def sub(a, b):
    return co(a, b, 'cmin')


def div(a, b):
    return co(a, b, 'cdiv')


def exp(a, b):
    return co(a, b, 'cexp')


def fz(a, b):
    return co(a, b, 'cfz')


def neg(a):
    return seq(a, 'cneg')


def summ(rng, body, v):
    return seq(rng, body, v, 'csu')


# Formulas.
def cel(a, b):
    return seq(a, b, 'wcel')


def br(a, b, r):
    return seq(a, b, r, 'wbr')


def lt(a, b):
    return br(a, b, 'clt')


def le(a, b):
    return br(a, b, 'cle')


def dvds(a, b):
    return br(a, b, 'cdvds')


def eq(a, b):
    return seq(a, b, 'wceq')


def ne(a, b):
    return seq(a, b, 'wne')


def wa(a, b):
    return seq(a, b, 'wa')


def wo(a, b):
    return seq(a, b, 'wo')


def wi(a, b):
    return seq(a, b, 'wi')


def wb(a, b):
    return seq(a, b, 'wb')


def wn(a):
    return seq(a, 'wn')


def w3a(a, b, c):
    return seq(a, b, c, 'w3a')


def rex(body, v, over):
    return seq(body, v, over, 'wrex')


class Builder:
    """Statements in set.mm's notation, proofs in stack order."""

    def __init__(self, sigs):
        self.sigs = sigs
        self._syntax = None
        self.flabel = {s.statement[1]: label
                       for label, s in sigs.items() if s.kind == '$f'}
        # What a statement asks to be pushed is every variable it mentions,
        # in the order set.mm declares the floats, which is the order they
        # are read in and not the order a statement happens to write them.
        self.forder = {label: i for i, label in enumerate(sigs)}

    @property
    def syntax(self):
        """set.mm's syntax axioms, built the first time one is parsed.

        Building them walks every signature in the library twice, and a
        caller that only applies labels never parses a statement, so the
        cost waits until `rpn` asks for it.
        """
        if self._syntax is None:
            self._syntax = kernel.Syntax(self.sigs)
        return self._syntax

    def define(self, label, statement):
        """Register a lemma this file proves, so a later one may apply it."""
        tokens = statement.split()
        free = sorted({t for t in tokens if t in self.flabel},
                      key=lambda v: self.forder[self.flabel[v]])
        self.sigs[label] = Signature(
            label, '$p', tokens,
            [(self.sigs[self.flabel[v]].statement[0], v) for v in free])

    def rpn(self, text, start='class'):
        """A term written in set.mm's notation, as the labels that build it."""
        return self.syntax.parse(text.split(), start).rpn(self.flabel)

    def wff(self, text):
        return self.rpn(text, 'wff')

    def spelt(self, binding):
        """A binding of kernel terms, as the strings `ap` wants pushed.

        A matcher answers in terms and `ap` pushes tokens, and this is the
        one step between them.
        """
        return {v: term.rpn(self.flabel) for v, term in binding.items()}

    def ap(self, label, binds=None, *essentials):
        """One step: what the label wants pushed, then what it is applied to.

        The floating hypotheses go first, in the order set.mm declares them,
        each as the term bound to it or as its own variable where the step
        leaves it open; then the proofs of the essential hypotheses, in the
        order the label lists them.
        """
        sig = self.sigs[label]
        out = [binds[var] if binds and var in binds else self.flabel[var]
               for _typecode, var in sig.floats]
        return self.seq(*out, *essentials, label)

    def seq(self, *parts):
        """Tokens in order, skipping any that are empty: a term or a proof.

        Reverse Polish says which by its last token. A term ends in the
        constructor that builds it — `wcel`, `wa`, `co` — and a proof in the
        assertion it applies, whose statement set.mm marks `|-`: `syl`,
        `a1i`, `readdcld`. So what is built is read off what was built. A
        proof comes back a `Proof` always, resting on what its parts rest on
        and on nothing where nothing on the page went into it; a term comes
        back as text, and a term built from a proof is a mistake, and
        refused.
        """
        text = ' '.join(p.text if type(p) is Proof else p for p in parts if p)
        held = [p.origin for p in parts if type(p) is Proof]
        last = self.sigs.get(text[text.rfind(' ') + 1:])
        if last is not None and last.statement[:1] == ['|-']:
            return Proof(text, frozenset().union(*held))
        if held:
            raise TypeError(f'a term built from a proof: …{text[-60:]}')
        return text
