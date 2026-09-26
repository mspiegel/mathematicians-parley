"""Where the readable layer's words land in set.mm.

`db/notation.records` and the `stdlib/*.records` files carry a `target` field
beside `metamath`, and this reads it. `metamath` says in words which set.mm
construct a pattern or an item corresponds to, which is what a person checking
the database wants; `target` says the same thing as a term, which is what a
program needs. Neither is derivable from the other, so both are written.

Which set.mm lemmas an elaborator may lean on for what the readable layer
never writes is not a database field either; `parley/rules.py` holds it.
"""
import re

HOLE = re.compile(r'_(\d+)')
FOLDED = 'folded'
REVERSED = 'equation reversed'
# What a `target` may say that is not a lemma: that a pattern builds another
# notation's tree, and that the lemma writes its equation the other way round
# from the `then` line. `DATABASE.md` documents both.
MARKERS = frozenset({FOLDED, REVERSED})


def split_entries(value):
    """The entries of a `target` field, one per pattern."""
    return [piece.strip() for piece in value.split(',') if piece.strip()]


def terms(records):
    """For each notation, the term each of its patterns builds.

    A folded pattern builds another notation's tree, so it has no entry of its
    own and is recorded as None.
    """
    out = {}
    for r in records:
        if r.kind != 'notation' or 'target' not in r.fields:
            continue
        out[r.name] = [None if e == FOLDED else e
                       for e in split_entries(r.fields['target'])]
    return out


def unfolding(record):
    """The theorem that unfolds a definition, and whether it faces the other
    way from the `then` line.
    """
    value = record.fields.get('target')
    if not value:
        return None, False
    entries = split_entries(value)
    return entries[0], any('reversed' in e for e in entries[1:])


def lemma(record):
    """The set.mm theorem an item corresponds to, and what fills it.

    A readable theorem and the lemma that supplies it are stated in different
    variables, and nothing derives the correspondence:
    `thm:stdlib/divisibility/not-both` is double negation and its `ph` is what
    the readable statement calls `n is even`. So the item says it, as
    `notnot with ph := n is even`, and each right-hand side is a formula in
    the item's own names.
    """
    value = record.fields.get('target')
    if not value or ' with ' not in value:
        return (value.strip() if value else None), {}
    head, _, rest = value.partition(' with ')
    fills = {}
    for piece in split_entries(rest):
        name, _, formula = piece.partition(':=')
        if formula:
            fills[name.strip()] = formula.strip()
    return head.strip(), fills


def commuting(records):
    """The terms whose two operands may be exchanged, from `commutes`.

    Each entry is the constructor, the two positions the holes occupy, and
    what stands in every other position: the product is `co` with holes at 0
    and 1 and `cmul` at 2. The positions are read off the target, so nothing
    here assumes where a constructor keeps its operator.
    """
    out = []
    for r in records:
        if r.kind != 'notation' or 'commutes' not in r.fields:
            continue
        says = split_entries(r.fields['commutes'])
        patterns = split_entries(r.fields.get('target', ''))
        for pattern, yes in zip(patterns, says, strict=False):
            places = slots(pattern)
            if yes != 'yes' or pattern == FOLDED or len(places) != 2:
                continue
            tokens = pattern.split()
            out.append((tokens[-1], tuple(sorted(places.values())),
                        {i: t for i, t in enumerate(tokens[:-1])
                         if i not in places.values()}))
    return out


def clauses(record):
    """The lemmas an item's `target` names, one per `then` group.

    An item may state several things at once —
    `thm:stdlib/numbers/real-closure` says a sum and a difference are both
    real — and set.mm proves each separately, so a step citing the item
    claims one of them.

    What stands before `with` is still a list, and the filling serves every
    lemma in it: `thm:proof/sqrt2-irrational/lowest-terms` is assembled from
    three theorems about a rational's numerator and denominator, and all
    three are about the same rational. What stands after it is the filling
    and not a list, however many commas it takes.
    """
    value = record.fields.get('target')
    if not value:
        return []
    return split_entries(lemma(record)[0] if ' with ' in value else value)


def fill(pattern, holes):
    """A target with its holes replaced by the terms filling them."""
    return HOLE.sub(lambda m: holes[int(m.group(1)) - 1], pattern)


def slots(pattern):
    """Which operand position each hole occupies, by hole number."""
    places = {}
    for i, token in enumerate(pattern.split()):
        found = HOLE.match(token)
        if found:
            places[int(found.group(1)) - 1] = i
    return places


# Numerals: the constant each digit builds.
NUMERALS = {'0': 'cc0', '1': 'c1', '2': 'c2', '3': 'c3', '4': 'c4',
            '5': 'c5', '6': 'c6', '7': 'c7', '8': 'c8', '9': 'c9'}
