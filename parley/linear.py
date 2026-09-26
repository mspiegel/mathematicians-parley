"""Linear arithmetic over an ordered field, as `METHODS.md` specifies it.

`inequalities` is the one closure method that needs a decision procedure
rather than a table of named laws. Deciding it is done here; emitting the
Metamath proof of what was decided is done in `normal.py`, because the two
are different jobs and only the second needs the kernel.

Everything rests on reading a term as a linear combination of **atoms**. An
atom is a maximal subterm not built from numerals by `+`, `−`, unary minus,
`·` by a numeral and `/` by a numeral, and a numeral over anything else is
that numeral times the reciprocal, which is the atom. The method never looks
inside one and
knows nothing about what it means: `|y|` is an atom, and that it is at least
`y` reaches a step as a cited line rather than as arithmetic.

A fact is a linear expression against zero. The five shapes `METHODS.md`
lists reduce to four by moving everything to one side and turning one
negation round, since `not (e <_ 0)` is `0 < e`. What is carried here is
`=`, `<_`, `<` and `=/=`, and the last is the one that splits: using it
means solving twice, once each side of the equation, and both must fail.
"""
from fractions import Fraction

# What a linear expression is built from, by the set.mm label of the
# operation. Anything else is an atom, however much arithmetic is inside it.
ADD, SUB, MUL, DIV, NEG = 'caddc', 'cmin', 'cmul', 'cdiv', 'cneg'
DIGITS = {'cc0': 0, 'c1': 1, 'c2': 2, 'c3': 3, 'c4': 4,
          'c5': 5, 'c6': 6, 'c7': 7, 'c8': 8, 'c9': 9}
ONE = 'c1'

# The relations a fact may carry, by the set.mm label that states it.
RELATIONS = {'clt': '<', 'cle': '<='}


class Linear:
    """A rational combination of atoms, plus a constant."""

    __slots__ = ('constant', 'weight')

    def __init__(self, weight=None, constant=0):
        self.weight = dict(weight or {})        # atom -> Fraction
        self.constant = Fraction(constant)

    def __repr__(self):
        said = [f'{v}*{k}' for k, v in sorted(self.weight.items()) if v]
        return ' + '.join([*said, str(self.constant)])

    def scaled(self, by):
        by = Fraction(by)
        return Linear({k: v * by for k, v in self.weight.items()},
                      self.constant * by)

    def plus(self, other):
        out = dict(self.weight)
        for atom, weight in other.weight.items():
            out[atom] = out.get(atom, Fraction(0)) + weight
        return Linear({k: v for k, v in out.items() if v},
                      self.constant + other.constant)

    def minus(self, other):
        return self.plus(other.scaled(-1))

    def atoms(self):
        return {k for k, v in self.weight.items() if v}

    def constant_only(self):
        return not self.atoms()


class Fact:
    """A linear expression standing in a relation to zero.

    `weights` says which of the facts the caller supplied this one was
    built from, and in what multiple. A fact straight from the caller is
    one times itself; one that elimination produced is the combination
    that produced it. Carrying it is what lets a refutation be turned
    into a proof rather than only a verdict.
    """

    __slots__ = ('how', 'side', 'weights', 'why')

    def __init__(self, side, how, why=None, weights=None):
        self.side, self.how = side, how         # `side how 0`, how in = <= <
        self.why = why                          # what the caller wants back
        self.weights = dict(weights or {})      # which given, times what

    def __repr__(self):
        return f'{self.side!r} {self.how} 0'

    def combined(self, other, mine, theirs):
        """This scaled by `mine` plus `other` scaled by `theirs`."""
        out = {k: v * mine for k, v in self.weights.items()}
        for k, v in other.weights.items():
            out[k] = out.get(k, Fraction(0)) + v * theirs
        return {k: v for k, v in out.items() if v}


def numeral(term, labels):
    """The value a term denotes, if it is built only from numerals."""
    if term.variable is not None:
        return None
    label = term.label
    if label in DIGITS:
        return Fraction(DIGITS[label])
    if label == NEG and len(term.children) == 1:
        inner = numeral(term.children[0], labels)
        return None if inner is None else -inner
    if label != 'co' or len(term.children) != 3:
        return None
    operation = term.children[2].rpn(labels)
    left = numeral(term.children[0], labels)
    right = numeral(term.children[1], labels)
    if left is None or right is None:
        return None
    if operation == ADD:
        return left + right
    if operation == SUB:
        return left - right
    if operation == MUL:
        return left * right
    if operation == DIV and right != 0:
        return left / right
    return None


def read(term, labels):
    """A term as a linear combination of atoms.

    What is not built from numerals by the operations above is an atom, and
    is keyed by the term it spells so that two occurrences of one subterm
    are one atom.
    """
    value = numeral(term, labels)
    if value is not None:
        return Linear(constant=value)
    if term.variable is None and term.label == NEG \
            and len(term.children) == 1:
        return read(term.children[0], labels).scaled(-1)
    if term.variable is None and term.label == 'co' \
            and len(term.children) == 3:
        operation = term.children[2].rpn(labels)
        left, right = term.children[0], term.children[1]
        if operation == ADD:
            return read(left, labels).plus(read(right, labels))
        if operation == SUB:
            return read(left, labels).minus(read(right, labels))
        if operation == MUL:
            by = numeral(right, labels)
            if by is not None:
                return read(left, labels).scaled(by)
            by = numeral(left, labels)
            if by is not None:
                return read(right, labels).scaled(by)
        if operation == DIV:
            by = numeral(right, labels)
            if by is not None and by != 0:
                return read(left, labels).scaled(Fraction(1) / by)
            # A numeral over a term is the numeral times the term's
            # reciprocal, and the reciprocal is the atom (`METHODS.md`).
            top = numeral(left, labels)
            if by is None and top is not None and top != 0:
                return Linear({f'{ONE} {right.rpn(labels)} {DIV} co': top})
    return Linear({term.rpn(labels): Fraction(1)})


def fact(term, labels, why=None):
    """A claim as a fact about zero, or None if it states no relation.

    The claim is moved to one side, so `a <_ b` becomes `a - b <_ 0`, and a
    negated relation is turned rather than carried: not (a <_ b) is b < a.
    A disequality is carried as one fact and split where it is used.
    """
    negated = False
    if term.variable is None and term.label == 'wn' \
            and len(term.children) == 1:
        negated, term = True, term.children[0]
    if term.variable is not None:
        return None
    if term.label == 'wceq' and len(term.children) == 2:
        side = read(term.children[0], labels).minus(
            read(term.children[1], labels))
        return Fact(side, '=/=' if negated else '=', why)
    if term.label != 'wbr' or len(term.children) != 3:
        return None
    how = RELATIONS.get(term.children[2].rpn(labels))
    if how is None:
        return None
    left = read(term.children[0], labels)
    right = read(term.children[1], labels)
    if not negated:
        return Fact(left.minus(right), how, why)
    # not (a < b) is b <_ a, and not (a <_ b) is b < a.
    return Fact(right.minus(left), '<=' if how == '<' else '<', why)


def opposite(one):
    """The fact that denies this one, for the refutation to start from."""
    if one.how == '=':
        return Fact(one.side, '=/=', one.why)
    if one.how == '=/=':
        return Fact(one.side, '=', one.why)
    return Fact(one.side.scaled(-1), '<=' if one.how == '<' else '<', one.why)


def refutes(facts):
    """Whether these facts have no solution over an ordered field."""
    return certificate(facts) is not None


def certificate(facts):
    """The multipliers that make these facts contradict, or None.

    Fourier–Motzkin: an equation is two inequalities, then one atom at a
    time is eliminated by adding every lower bound to every upper bound.
    What is left is constants, and the set fails when one of them is a
    constant standing in a relation no number satisfies.

    What is returned is Farkas's combination — each given fact and the
    multiple of it that goes into the contradiction. An inequality may
    only be multiplied by something positive; an equation by anything,
    which is why its two halves carry opposite signs. A proof of the step
    is built from that combination, so it is kept rather than discarded.

    A disequality is the one fact with two readings, so it is taken both
    ways and the set fails only when both do. There is then no single
    combination, and `('either', i, one, other)` says so.
    """
    for i, one in enumerate(facts):
        if one.how == '=/=':
            rest = [*facts[:i], *facts[i + 1:]]
            first = certificate([*rest, Fact(one.side, '<')])
            if first is None:
                return None
            second = certificate([*rest, Fact(one.side.scaled(-1), '<')])
            return None if second is None else ('either', i, first, second)
    open_facts = []
    for i, one in enumerate(facts):
        if one.how == '=':
            open_facts.append(Fact(one.side, '<=', weights={i: Fraction(1)}))
            open_facts.append(Fact(one.side.scaled(-1), '<=',
                                   weights={i: Fraction(-1)}))
        else:
            open_facts.append(Fact(one.side, one.how,
                                   weights={i: Fraction(1)}))
    atoms = sorted({a for f in open_facts for a in f.side.atoms()})
    for atom in atoms:
        under, over, rest = [], [], []
        for one in open_facts:
            weight = one.side.weight.get(atom, Fraction(0))
            if weight > 0:
                over.append(one)
            elif weight < 0:
                under.append(one)
            else:
                rest.append(one)
        joined = []
        for high in over:
            for low in under:
                a = high.side.weight[atom]
                b = -low.side.weight[atom]
                made = high.side.scaled(b).plus(low.side.scaled(a))
                how = '<' if '<' in (high.how, low.how) else '<='
                joined.append(Fact(made, how,
                                   weights=high.combined(low, b, a)))
        open_facts = rest + joined
        if len(open_facts) > 400:
            return None                          # past anything the corpus has
    for one in open_facts:
        if not one.side.constant_only():
            continue
        if (one.how == '<' and one.side.constant >= 0) \
                or (one.how == '<=' and one.side.constant > 0):
            return one.weights
    return None


def follows(given, claim):
    """Whether the claim follows from the given facts.

    The claim is denied and the set shown to have no solution. Denying an
    equation gives a disequality, which is the one fact that splits, so an
    equation concluded and a disequality cited cost the same.
    """
    return refutes([*given, opposite(claim)])
