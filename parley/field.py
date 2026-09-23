"""Equality of rational expressions over a field, as `METHODS.md` has it.

`algebra` is the second method that decides rather than looks up, and it
differs from `inequalities` in two ways: it is not restricted to linear
expressions, and it knows nothing about order. Deciding it is done here;
emitting the Metamath proof of what was decided is `normal.py`, which
`elaborate.py` drives.

An atom is a maximal subterm not built from numerals by `+`, `−`, unary
minus, `·`, `/`, and powers **with a numeral exponent**. The exponent rule
is the whole of the boundary: in `(2k + 1)² = 4k² + 4k + 1` the exponent is
2, so the square is expanded and the only atom is `k`; in `2^k + 2^k = 2^k·2`
the exponent is a variable, so `2^k` is an atom and the step is `x + x = x·2`.

A term reads as a quotient of two polynomials over those atoms. Two are
equal when the cross product of their numerators and denominators vanishes,
which is the identity the corpus's steps state; that the denominators are
not zero is a hypothesis the text writes as a `requires` line, and is not
decided here.
"""
from fractions import Fraction

from parse import Declined, declined

ADD, SUB, MUL, DIV, EXP, NEG = 'caddc', 'cmin', 'cmul', 'cdiv', 'cexp', 'cneg'
DIGITS = {'cc0': 0, 'c1': 1, 'c2': 2, 'c3': 3, 'c4': 4,
          'c5': 5, 'c6': 6, 'c7': 7, 'c8': 8, 'c9': 9}
NUMERAL = {v: k for k, v in DIGITS.items()}
CAP = 24                     # an exponent past anything the corpus writes


class Poly:
    """A polynomial over atoms, as coefficients by monomial.

    A monomial is a tuple of (atom, power) in atom order, so the empty tuple
    is the constant one and two spellings of a product are one key.
    """

    __slots__ = ('terms',)

    def __init__(self, terms=None):
        self.terms = {k: v for k, v in (terms or {}).items() if v}

    def __repr__(self):
        if not self.terms:
            return '0'
        return ' + '.join(
            f'{v}' + ''.join(f'*{a}^{p}' for a, p in m)
            for m, v in sorted(self.terms.items()))

    def __eq__(self, other):
        return self.terms == other.terms

    def __hash__(self):
        return hash(frozenset(self.terms.items()))

    def zero(self):
        return not self.terms

    def plus(self, other):
        out = dict(self.terms)
        for monomial, weight in other.terms.items():
            out[monomial] = out.get(monomial, Fraction(0)) + weight
        return Poly(out)

    def scaled(self, by):
        return Poly({k: v * Fraction(by) for k, v in self.terms.items()})

    def minus(self, other):
        return self.plus(other.scaled(-1))

    def times(self, other):
        out = {}
        for left, a in self.terms.items():
            for right, b in other.terms.items():
                monomial = _join(left, right)
                out[monomial] = out.get(monomial, Fraction(0)) + a * b
        return Poly(out)

    def power(self, by):
        out = one()
        for _ in range(by):
            out = out.times(self)
        return out


def _join(left, right):
    """One monomial from two, adding the powers of a shared atom."""
    powers = dict(left)
    for atom, power in right:
        powers[atom] = powers.get(atom, 0) + power
    return tuple(sorted((a, p) for a, p in powers.items() if p))


def constant(value):
    return Poly({(): Fraction(value)})


def one():
    return constant(1)


def atom(said):
    return Poly({((said, 1),): Fraction(1)})


def order(monomial):
    """Descending degree, then by atom.

    The order a polynomial is written in, so that `4m^2 + 4m + 1` comes out
    that way round rather than the other.
    """
    return (-sum(power for _, power in monomial), monomial)


def spell_monomial(monomial):
    """One monomial in reverse Polish, as a product of powers.

    Every factor is written `( x ^ k )`, the exponent one included, and
    the empty monomial is `1`. The product associates to the left.
    """
    if not monomial:
        return NUMERAL[1]
    said = [f'{atom} {NUMERAL[power]} cexp co' for atom, power in monomial]
    out = said[0]
    for one in said[1:]:
        out = f'{out} {one} cmul co'
    return out


def spell_coefficient(weight):
    """A rational coefficient as a numeral, negated where it is negative.

    None where it is not a whole number the kernel has one digit for,
    which is past anything this corpus writes.
    """
    if weight.denominator != 1 or abs(weight.numerator) > 9:
        return None
    digit = NUMERAL[abs(weight.numerator)]
    return f'{digit} cneg' if weight.numerator < 0 else digit


def spell(poly):
    """A polynomial as one term in reverse Polish: the canonical form.

    Both sides of an `algebra` step are driven to this, and the step is
    then the two of them being the same term. Sums associate to the left
    and run down in degree, and every term is `( c x. M )` with no case
    left out: a coefficient of one is written, so is an exponent of one,
    and the constant term is `( c x. 1 )`. That is not how anyone writes
    a polynomial, and it does not have to be — the form is internal, the
    claim stays the two terms the text wrote. What it buys is that every
    step of the arithmetic over these forms has one shape to handle
    rather than four.

    None where a coefficient is past what `spell_coefficient` writes.
    """
    if not poly.terms:
        return NUMERAL[0]
    said = []
    for monomial in sorted(poly.terms, key=order):
        digit = spell_coefficient(poly.terms[monomial])
        if digit is None:
            return None
        said.append(f'{digit} {spell_monomial(monomial)} cmul co')
    out = said[0]
    for one in said[1:]:
        out = f'{out} {one} caddc co'
    return out


class Quotient:
    """A polynomial over a polynomial, which is what a term reads as."""

    __slots__ = ('over', 'under')

    def __init__(self, over, under=None):
        self.over, self.under = over, under or one()

    def __repr__(self):
        return f'({self.over!r}) / ({self.under!r})'

    def plus(self, other):
        return Quotient(self.over.times(other.under)
                        .plus(other.over.times(self.under)),
                        self.under.times(other.under))

    def minus(self, other):
        return self.plus(Quotient(other.over.scaled(-1), other.under))

    def times(self, other):
        return Quotient(self.over.times(other.over),
                        self.under.times(other.under))

    def over_under(self, other):
        return Quotient(self.over.times(other.under),
                        self.under.times(other.over))

    def power(self, by):
        return Quotient(self.over.power(by), self.under.power(by))


def numeral(term, labels):
    """The whole number a term denotes, if it denotes one."""
    if term.variable is not None:
        return None
    if term.label in DIGITS:
        return DIGITS[term.label]
    if term.label == NEG and len(term.children) == 1:
        inner = numeral(term.children[0], labels)
        return None if inner is None else -inner
    return None


def read(term, labels):
    """A term as a quotient of polynomials over its atoms."""
    whole = numeral(term, labels)
    if whole is not None:
        return Quotient(constant(whole))
    if term.variable is None and term.label == NEG \
            and len(term.children) == 1:
        inner = read(term.children[0], labels)
        return Quotient(inner.over.scaled(-1), inner.under)
    if term.variable is None and term.label == 'co' \
            and len(term.children) == 3:
        how = term.children[2].rpn(labels)
        left, right = term.children[0], term.children[1]
        if how == ADD:
            return read(left, labels).plus(read(right, labels))
        if how == SUB:
            return read(left, labels).minus(read(right, labels))
        if how == MUL:
            return read(left, labels).times(read(right, labels))
        if how == DIV:
            under = read(right, labels)
            if not under.over.zero():
                return read(left, labels).over_under(under)
        if how == EXP:
            # The exponent rule: a numeral exponent is expanded, and any
            # other leaves the whole power an atom.
            by = numeral(right, labels)
            if by is not None and 0 <= by <= CAP:
                return read(left, labels).power(by)
    return Quotient(atom(term.rpn(labels)))


def equation(term, labels):
    """A claim as a polynomial that must vanish, or None if it is not one."""
    if term.variable is not None or term.label != 'wceq':
        return None
    if len(term.children) != 2:
        return None
    left = read(term.children[0], labels)
    right = read(term.children[1], labels)
    # p/q = r/s exactly when ps - rq vanishes, the denominators being the
    # nonzero conditions the text writes as `requires` lines.
    return left.over.times(right.under).minus(right.over.times(left.under))


def denied(term, labels):
    """The polynomial a disequality says does not vanish, or None.

    The corpus writes `a ≠ 1` as a negated equation, which the `negates`
    line of `db/notation.records` folds into one tree, so what arrives here
    is a `wn` around the equation and the polynomial is the equation's.
    """
    if term.variable is not None or term.label != 'wn':
        return None
    if len(term.children) != 1:
        return None
    return equation(term.children[0], labels)


def follows(given, claim, atoms):
    """How the claim is a combination of the given equations, or None.

    With nothing cited the claim must vanish outright, which is twelve of
    the corpus's seventeen steps, and the combination is empty. With
    equations cited it must be a combination of them — ideal membership —
    and `ELABORATION.md` measures every such step in the corpus: the
    multipliers are constants but for one, whose multiplier is a single
    atom. So the multipliers looked for are a rational times a monomial of
    degree at most one, and nothing is searched for past that.

    What is returned is the combination itself, one `(which, shape, scale)`
    for each equation taken off: the claim is their sum. A proof of the step
    is built from it, so it is kept rather than discarded, as
    `linear.certificate` keeps Farkas's.
    """
    if claim.zero():
        return []
    if not given:
        return None
    shapes = [one(), *(atom(a) for a in sorted(atoms))]
    return _reduces(claim, given, shapes)


def _reduces(claim, given, shapes, depth=3):
    """Take one cited equation off the claim, by some allowed multiplier."""
    if claim.zero():
        return []
    if depth <= 0:
        return None
    for which, held in enumerate(given):
        if held.zero():
            continue
        for shape in shapes:
            scale = _cancels(claim, held.times(shape))
            if scale is None:
                continue
            rest = _reduces(claim.minus(held.times(shape).scaled(scale)),
                            given, shapes, depth - 1)
            if rest is not None:
                return [(which, shape, scale), *rest]
    return None


def _cancels(claim, part):
    """The rational that makes this part cancel the claim's leading term.

    The leading term is the largest monomial the claim has, in the order the
    keys sort in, so taking it off strictly shrinks what is left.
    """
    if part.zero():
        return None
    lead = max(claim.terms)
    if lead not in part.terms:
        return None
    if max(part.terms) != lead:
        return None
    return claim.terms[lead] / part.terms[lead]


# --- closed numeral claims, which `arithmetic` decides ----------------------

# A number more than this many bits long is not worked out. Python's integers
# do not wrap round, so what a claim like 9^(9^9) costs is time and memory
# without end, and it is refused before it is computed. The corpus's largest
# number is 10; ten thousand bits is some three thousand digits.
BITS = 10_000

# The number systems a closed number is tested for membership of, by
# `METHODS.md`'s tests on its value.
SYSTEM_TESTS = {
    'cn': lambda v: v.denominator == 1 and v > 0,
    'cn0': lambda v: v.denominator == 1 and v >= 0,
    'cz': lambda v: v.denominator == 1,
    'cq': lambda v: True,
    'cr': lambda v: True,
    'cc': lambda v: True,
}
ORDER = {'clt': lambda a, b: a < b, 'cle': lambda a, b: a <= b}


class Unworked:
    """A closed term that has no exact value to give, and why.

    It divides by zero, it is too large to work out, or it is not rational.
    """

    __slots__ = ('reason',)

    def __init__(self, reason):
        self.reason = reason


class Verdict:
    """What a closed claim comes to.

    `holds` is True or False where the claim was worked out, and `reason`
    says why it could not be where it was not.
    """

    __slots__ = ('holds', 'reason')

    def __init__(self, holds, reason=''):
        self.holds, self.reason = holds, reason


def _too_large(value):
    return max(value.numerator.bit_length(),
               value.denominator.bit_length()) > BITS


def closed_value(term, labels):
    """The exact value of a term built from numerals alone.

    A `Fraction`, never a float: `int / int`, a negative power of an int and
    a fractional power all give floats, which may be inexact, `inf` or `0.0`
    with no error, so every value is a `Fraction` from the numeral up and an
    exponent is whole before it is used. An `Unworked` where the term has no
    exact value, and a decline where it is not built from numerals at all.
    """
    if term.variable is not None:
        return Declined('it holds a letter')
    if term.label in DIGITS and not term.children:
        return Fraction(DIGITS[term.label])
    if term.label == 'cdc' and len(term.children) == 2:
        parts = [closed_value(c, labels) for c in term.children]
        stop = _first_stop(parts)
        if stop is not None:
            return stop
        value = parts[0] * 10 + parts[1]
    elif term.label == NEG and len(term.children) == 1:
        inner = closed_value(term.children[0], labels)
        if declined(inner) or isinstance(inner, Unworked):
            return inner
        value = -inner
    elif term.label == 'co' and len(term.children) == 3:
        how = term.children[2].label
        parts = [closed_value(c, labels) for c in term.children[:2]]
        stop = _first_stop(parts)
        if stop is not None:
            return stop
        left, right = parts
        if how == ADD:
            value = left + right
        elif how == SUB:
            value = left - right
        elif how == MUL:
            value = left * right
        elif how == DIV:
            if right == 0:
                return Unworked('divides by zero')
            value = left / right
        elif how == EXP:
            if right.denominator != 1:
                return Unworked('is not a rational number: its exponent is '
                                'not whole')
            power = int(right)
            if left == 0 and power < 0:
                return Unworked('divides by zero')
            size = max(left.numerator.bit_length(),
                       left.denominator.bit_length())
            if size * abs(power) > BITS:
                return Unworked('is too large to work out')
            value = left ** power
        else:
            return Declined('not an operation arithmetic reads')
    else:
        return Declined('not built from numerals')
    if type(value) is not Fraction:
        return Unworked('is not an exact number')
    if _too_large(value):
        return Unworked('is too large to work out')
    return value


def _first_stop(parts):
    """The first part that is not a value, a decline before an `Unworked`."""
    for part in parts:
        if declined(part):
            return part
    for part in parts:
        if isinstance(part, Unworked):
            return part
    return None


def decide_closed(claim, labels):
    """Whether a relation between closed numeral terms holds.

    `METHODS.md`'s procedure for `arithmetic`: evaluate each side to a
    rational and decide the relation, or for a membership test the value.
    `=`, `≠`, `<` and `≤` — a reader's `>` and `≥` arrive as these with the
    sides turned — denials of any of them, and membership of ℕ, ℕ₀, ℤ, ℚ,
    ℝ and ℂ. A decline where the claim is none of these or holds a letter;
    a `Verdict` otherwise.
    """
    negated = claim.label == 'wn' and len(claim.children) == 1
    if negated:
        claim = claim.children[0]
    if claim.label in ('wceq', 'wne') and len(claim.children) == 2:
        sides = claim.children
        holds = ((lambda a, b: a == b) if claim.label == 'wceq'
                 else (lambda a, b: a != b))
    elif claim.label == 'wbr' and len(claim.children) == 3 \
            and claim.children[2].label in ORDER:
        sides, holds = claim.children[:2], ORDER[claim.children[2].label]
    elif claim.label == 'wcel' and len(claim.children) == 2 \
            and claim.children[1].label in SYSTEM_TESTS \
            and not claim.children[1].children:
        test = SYSTEM_TESTS[claim.children[1].label]
        sides, holds = claim.children[:1], (lambda a: test(a))
    else:
        return Declined('not a relation arithmetic decides')
    values = [closed_value(side, labels) for side in sides]
    stop = _first_stop(values)
    if declined(stop):
        return stop
    if stop is not None:
        return Verdict(None, stop.reason)
    return Verdict(holds(*values) != negated)
