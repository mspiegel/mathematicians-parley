"""Equality of rational expressions over a field, as `METHODS.md` has it.

`algebra` is the second method that decides rather than looks up, and it
differs from `inequalities` in two ways: it is not restricted to linear
expressions, and it knows nothing about order. Deciding it is done here;
emitting the Metamath proof of what was decided is `elaborate.py`.

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

ADD, SUB, MUL, DIV, EXP, NEG = 'caddc', 'cmin', 'cmul', 'cdiv', 'cexp', 'cneg'
DIGITS = {'cc0': 0, 'c1': 1, 'c2': 2, 'c3': 3, 'c4': 4,
          'c5': 5, 'c6': 6, 'c7': 7, 'c8': 8, 'c9': 9}
NUMERAL = {v: k for k, v in DIGITS.items()}
CAP = 24                     # an exponent past anything the corpus writes


class Poly:
    """A polynomial over atoms, as coefficients by monomial.

    A monomial is a tuple of (atom, power) in atom order, so the empty tuple
    is the constant one and two spellings of a product are one key."""

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
    that way round rather than the other."""
    return (-sum(power for _, power in monomial), monomial)


def spell_monomial(monomial):
    """One monomial in reverse Polish, as a product of powers.

    Every factor is written `( x ^ k )`, the exponent one included, and
    the empty monomial is `1`. The product associates to the left."""
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
    which is past anything this corpus writes."""
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

    None where a coefficient is past what `spell_coefficient` writes."""
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


def follows(given, claim, atoms):
    """Whether the claim is an identity, or follows from the given equations.

    With nothing cited the claim must vanish outright, which is twelve of
    the corpus's seventeen steps. With equations cited it must be a
    combination of them — ideal membership — and `ELABORATION.md` measures
    every such step in the corpus: the multipliers are constants but for
    one, whose multiplier is a single atom. So the multipliers looked for
    are a rational times a monomial of degree at most one, and nothing is
    searched for past that."""
    if claim.zero():
        return True
    if not given:
        return False
    shapes = [one(), *(atom(a) for a in sorted(atoms))]
    return _reduces(claim, given, shapes)


def _reduces(claim, given, shapes, depth=3):
    """Take one cited equation off the claim, by some allowed multiplier."""
    if claim.zero():
        return True
    if depth <= 0:
        return False
    for held in given:
        if held.zero():
            continue
        for shape in shapes:
            scale = _cancels(claim, held.times(shape))
            if scale is None:
                continue
            if _reduces(claim.minus(held.times(shape).scaled(scale)),
                        given, shapes, depth - 1):
                return True
    return False


def _cancels(claim, part):
    """The rational that makes this part cancel the claim's leading term.

    The leading term is the largest monomial the claim has, in the order the
    keys sort in, so taking it off strictly shrinks what is left."""
    if part.zero():
        return None
    lead = max(claim.terms)
    if lead not in part.terms:
        return None
    if max(part.terms) != lead:
        return None
    return claim.terms[lead] / part.terms[lead]
