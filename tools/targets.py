"""Where the readable layer's words land in set.mm.

`db/notation.db` and `db/items.db` both carry a `metamath` field, and neither
is enough to elaborate with. The notation field says which constructor a
pattern targets, but six of the records write it as prose — "cexp with the
numeral 2", "wbr with cdvds" — because it was written for a person checking
that a label exists. The item field says what a definition *means*, not which
set.mm theorem performs the unfolding: `def:odd` names `not 2 ∥ n`, which is
the statement, where an elaborator needs `odd2np1`, which is the bridge.

So this module holds what the databases do not yet say. It is small and it is
the shape of a field those files are missing, not a store of expansions: every
entry is a name, never a proof.
"""

# How a notation's tree becomes a term. `wrap` says what encloses the
# children: None for a constructor that takes them directly, 'co' for an
# operation, 'wbr' for a relation, 'cfv' for a function application.
TERMS = {
    'number-systems': [('cn', None), ('cn0', None), ('cz', None),
                       ('cq', None), ('cr', None)],
    'membership': [('wcel', None), ('wnel', None)],
    'equality': [('wceq', None), ('wne', None)],
    'additive': [('caddc', 'co'), ('cmin', 'co')],
    'multiplicative': [('cmul', 'co'), ('cdiv', 'co')],
    'juxtaposition': [('cmul', 'co')],
    'unary-minus': [('cneg', None)],
    'power': [('cexp', 'co')],
    'square-root': [('csqrt', 'cfv')],
    'logical-not': [('wn', None)],
    'conjunction': [('wa', None)],
    'comma-conjunction': [('wa', None)],
    'disjunction': [('wo', None)],
    'implication': [('wi', None)],
    'divides': [('cdvds', 'wbr')],
}

# Patterns whose term is not one constructor applied to the children.
# `_²` is a power with a numeral the text does not write, and `n is even` and
# `n is odd` are a divisibility by a 2 the text does not write either.
SHAPES = {
    'square': 'square',
    'parity': 'parity',
}

# The theorem that unfolds a definition, which is not what `metamath` names.
# `def:odd` says `not 2 ∥ n`; odd2np1 is what turns that into the existential
# the readable definition states, and it is used in both directions.
# The second entry says the lemma writes the equation the other way round
# from the readable definition.
UNFOLD = {
    'def:odd': ('odd2np1', True),
    'def:even': ('divides', True),
}

# Closure: the lemma that puts a shape in a set, by the shape of the term.
CLOSURE = {
    ('cz', 'additive'): 'zaddcl',
    ('cz', 'multiplicative'): 'zmulcl',
    ('cz', 'juxtaposition'): 'zmulcl',
    ('cz', 'square'): 'zsqcl',
    ('cc', 'additive'): 'addcl',
    ('cc', 'multiplicative'): 'mulcl',
    ('cc', 'juxtaposition'): 'mulcl',
    ('cc', 'square'): 'sqcl',
}

# Moving a name from the set it was introduced in to the one a step needs.
WIDEN = {('cz', 'cr'): 'zre', ('cz', 'cc'): 'zcn', ('cr', 'cc'): 'recn'}

# Numerals, and how a numeral says it is in a set: `2z`, `2cn`, `2re`.
NUMERALS = {'0': 'cc0', '1': 'c1', '2': 'c2', '3': 'c3', '4': 'c4',
            '5': 'c5', '6': 'c6', '7': 'c7', '8': 'c8', '9': 'c9'}
NUMERAL_IN = {'cz': 'z', 'cc': 'cn', 'cr': 're', 'cn': 'nn', 'cq': 'q'}
