"""Where the readable layer's words land in set.mm.

`db/notation.db` and `db/items.db` carry a `target` field beside `metamath`,
and this reads it. `metamath` says in words which set.mm construct a pattern
or an item corresponds to, which is what a person checking the database
wants; `target` says the same thing as a term, which is what a program needs.
Neither is derivable from the other, so both are written.

What is still here rather than in the databases is closure: which set.mm
lemma puts a sum of integers in ℤ, and which moves an integer into ℂ. That is
a fact about set.mm's library rather than about the readable corpus, and no
field of a readable database is the place for it.
"""
import re

HOLE = re.compile(r'_(\d+)')
FOLDED = 'folded'


def split_entries(value):
    """The entries of a `target` field, one per pattern."""
    return [piece.strip() for piece in value.split(',') if piece.strip()]


def terms(records):
    """For each notation, the term each of its patterns builds.

    A folded pattern builds another notation's tree, so it has no entry of its
    own and is recorded as None."""
    out = {}
    for r in records:
        if r.kind != 'notation' or 'target' not in r.fields:
            continue
        out[r.name] = [None if e == FOLDED else e
                       for e in split_entries(r.fields['target'])]
    return out


def unfolding(record):
    """The theorem that unfolds a definition, and whether it faces the other
    way from the `then` line."""
    value = record.fields.get('target')
    if not value:
        return None, False
    entries = split_entries(value)
    return entries[0], any('reversed' in e for e in entries[1:])


def lemma(record):
    """The set.mm theorem an item corresponds to, and what fills it.

    A readable theorem and the lemma that supplies it are stated in different
    variables, and nothing derives the correspondence: `thm:not-both` is
    double negation and its `ph` is what the readable statement calls `n is
    even`. So the item says it, as `notnot with ph := n is even`, and each
    right-hand side is a formula in the item's own names."""
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


def fill(pattern, holes):
    """A target with its holes replaced by the terms that stand in them."""
    return HOLE.sub(lambda m: holes[int(m.group(1)) - 1], pattern)


def slots(pattern):
    """Which operand position each hole occupies, by hole number."""
    places = {}
    for i, token in enumerate(pattern.split()):
        found = HOLE.match(token)
        if found:
            places[int(found.group(1)) - 1] = i
    return places


# Closure: the lemma that puts a shape in a set, by the shape of the term.
CLOSURE = {
    ('cz', 'additive'): 'zaddcl',
    ('cz', 'multiplicative'): 'zmulcl',
    ('cz', 'square'): 'zsqcl',
    ('cc', 'additive'): 'addcl',
    ('cc', 'multiplicative'): 'mulcl',
    ('cc', 'square'): 'sqcl',
}

# Moving a name from the set it was introduced in to the one a step needs.
WIDEN = {('cz', 'cr'): 'zre', ('cz', 'cc'): 'zcn', ('cr', 'cc'): 'recn',
         ('cn', 'cz'): 'nnz', ('cn', 'cr'): 'nnre', ('cn', 'cc'): 'nncn',
         ('cn0', 'cz'): 'nn0z', ('cn0', 'cr'): 'nn0re',
         ('cn0', 'cc'): 'nn0cn', ('cq', 'cr'): 'qre', ('cq', 'cc'): 'qcn'}

# Numerals, and how a numeral says it is in a set: `2z`, `2cn`, `2re`.
NUMERALS = {'0': 'cc0', '1': 'c1', '2': 'c2', '3': 'c3', '4': 'c4',
            '5': 'c5', '6': 'c6', '7': 'c7', '8': 'c8', '9': 'c9'}
NUMERAL_IN = {'cz': 'z', 'cc': 'cn', 'cr': 're', 'cn': 'nn', 'cq': 'q'}

# Every lemma the elaborator may use to settle a membership, tried by matching
# its conclusion against what is wanted. A closed one settles it outright, one
# with an antecedent leaves that antecedent to settle in turn, and a
# biconditional is read left to right. The two tables above say some of this
# by shape; this list says it by statement, which is what a membership the
# readable layer never writes needs — `k e. CC` because k runs over a range of
# integers, say. It is declared rather than searched for: an elaborator that
# hunted through set.mm for anything that fitted would settle side conditions
# by means the text never names.
MEMBERSHIP = [
    'ax-1cn', '1re', '1z', '1nn', '2cn', '2re', '2z', '2nn', '0cn', '0re',
    '3cn', '3re', '3z', '4cn', '4re', '4z',
    'nnz', 'nnre', 'nncn', 'nn0z', 'nn0re', 'nn0cn', 'zre', 'zcn', 'recn',
    'qre', 'qcn', 'elnnuz',
    'elfzelz', 'abscl', 'zaddcl', 'zsubcl', 'zmulcl', 'zsqcl',
    'addcl', 'subcl', 'mulcl', 'sqcl', 'readdcl', 'remulcl', 'resqcl',
    'renegcl', 'negcl',
    # and what an order relation asks, which is the same kind of thing
    'ltle', 'ltnri', 'leid',
]
