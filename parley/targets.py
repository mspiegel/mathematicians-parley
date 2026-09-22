"""Where the readable layer's words land in set.mm.

`db/notation.records` and `db/items.records` carry a `target` field beside `metamath`,
and this reads it. `metamath` says in words which set.mm construct a pattern
or an item corresponds to, which is what a person checking the database
wants; `target` says the same thing as a term, which is what a program needs.
Neither is derivable from the other, so both are written.

What is still here rather than in the databases is `MEMBERSHIP`: which
set.mm lemmas an elaborator may lean on for what the readable layer never
writes. That a sum of integers is an integer, that an integer is a real,
that two integers may be multiplied either way round — these are facts
about set.mm's library rather than about the readable corpus, and no field
of a readable database is the place for them.

They were once four tables, one per shape of question. They are one list
tried by matching, because they were one question all along: what does
set.mm already prove that says this?
"""
import re

HOLE = re.compile(r'_(\d+)')
# A name the pattern has no hole for, standing for what the definition that
# introduced the notation fixed it to. `G(_)` is the sum of the powers of `a`
# and shows only the limit, so its target writes `@a` for the base.
FIXED = re.compile(r'@(\w+)')
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
    variables, and nothing derives the correspondence: `thm:not-both` is
    double negation and its `ph` is what the readable statement calls `n is
    even`. So the item says it, as `notnot with ph := n is even`, and each
    right-hand side is a formula in the item's own names.
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

    An item may state several things at once — `thm:real-closure` says a sum
    and a difference are both real — and set.mm proves each separately, so a
    step citing the item claims one of them.

    What stands before `with` is still a list, and the filling serves every
    lemma in it: `thm:lowest-terms` is assembled from three theorems about
    a rational's numerator and denominator, and all three are about the
    same rational. What stands after it is the filling and not a list,
    however many commas it takes.
    """
    value = record.fields.get('target')
    if not value:
        return []
    return split_entries(lemma(record)[0] if ' with ' in value else value)


def fixes(pattern):
    """The names a target holds fixed, in the order it writes them."""
    return FIXED.findall(pattern) if pattern else []


def fill(pattern, holes, fixed=()):
    """A target with its holes and its fixed names replaced by their terms.

    A hole is filled from the node being read and a fixed name from where
    the notation's definition fixed it, which is why they are two arguments
    and not one.
    """
    said = HOLE.sub(lambda m: holes[int(m.group(1)) - 1], pattern)
    return FIXED.sub(lambda m: fixed[m.group(1)], said) if fixed else said


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

# Every lemma the elaborator may lean on for a fact the text does not write,
# tried by matching its conclusion against what is wanted. A closed one
# settles it outright, one with an antecedent leaves that antecedent to
# settle in turn, and a biconditional is read whichever way reaches it.
#
# Saying it by statement rather than by shape is what lets one list answer
# every side condition there is: `k e. CC` because k runs over a range of
# integers, `( p ^ 2 ) e. ZZ` because p is one, `{ x e. A | ph } e. _V`
# because A is a set. It is declared rather than searched for: an elaborator
# that hunted through set.mm for anything that fitted would settle side
# conditions by means the text never names.
MEMBERSHIP = [
    'ax-1cn', '1re', '1z', '1nn', '2cn', '2re', '2z', '2nn', '0cn', '0re',
    '0z', '0nn0', '3cn', '3re', '3z', '4cn', '4re', '4z',
    'nnz', 'nnre', 'nncn', 'nnnn0', 'nn0z', 'nn0re', 'nn0cn',
    'zre', 'zcn', 'recn',
    'qre', 'qcn', 'elnnuz', 'eluz2', 'eluz2b1', 'eluz2b2', 'eluz2gt1',
    # Where a restriction sits is not what a claim says, and set.mm states
    # that in general: quantifying over a subset is quantifying over the set
    # with membership of the subset in the body. `exprmfct` puts primality in
    # the domain where the readable line puts it in the body.
    'rexss', 'prmssnn',
    # A summation index runs over a range of integers, and what the summand
    # asks of it is not always integrality: a power wants its exponent in
    # ℕ₀, which over `( 0 ... n )` the range itself gives.
    'elfzelz', 'elfznn0', 'abscl', 'zaddcl', 'zsubcl', 'zmulcl', 'zsqcl',
    'addcl', 'subcl', 'mulcl', 'sqcl', 'readdcl', 'remulcl', 'resqcl',
    'renegcl', 'negcl', 'reexpcl', 'nn0expcl', '2nn0', 'peano2nn0',
    # and what a commuting pair asks, which `db/notation.records` declares by
    # notation and this answers by statement
    'mulcom', 'addcom',
    # and sethood, which set theory asks where arithmetic asks closure
    'rabexg', 'ssexg', 'difexg', 'pwexg', 'unexg', 'rnexg', 'mptexg', '0ex',
    # A name a `fix` or an `obtain` introduces is a setvar, and a setvar is
    # a set by the kernel's own reckoning. `elpwg` asks it of whatever it
    # puts in a power set, and a proof that fixed the thing has nothing to
    # say about it that `vex` does not.
    'vex', 'snidg', 'snex',
    # A map sends no two things to the same place, which is what the readable
    # layer says, and set.mm reaches equinumerosity from it through the map
    # itself — one-to-one, then onto its own range. Neither of those is
    # anything a proof writes, which is what puts them here.
    'f1f1orn', 'f1mpt',
    # and finiteness, which the readable layer never says at all. It counts
    # a set and the count is a natural number, and every lemma about
    # cardinality asks for `e. Fin` instead. `hashvnfin` is set.mm saying
    # those come to the same thing, so the subsets proof reaches `Fin`
    # from what it does write rather than from a word added to every line.
    # `enfi` is the other way in: a set counted by being put beside one
    # already counted has no size of its own yet, and the bijection is
    # what says it is finite.
    'hashvnfin', 'enfi',
    # A claim that there is one of a thing and says nothing about it is
    # nonemptiness, and the corpus writes it with a name for the element:
    # `there is s ∈ S` builds a restricted existential whose body is T..
    # set.mm says the same thing three ways and relates them, so a line
    # putting something in the set reaches it.
    'ne0i', 'n0', 'rextru',
    # and what an order relation asks, which is the same kind of thing
    'ltle', 'ltnri', 'leid', 'nn0ge0', 'nngt0',
    # A lemma stated over the integers asks what a natural number being one
    # does not say in those words: `divalg` divides by anything but zero,
    # and the readable statement divides by a natural number. It bounds by
    # the absolute value for the same reason, which over ℕ₀ is no bound at
    # all.
    'nnne0',
    # The two equations in this list, and what `said_otherwise` rewrites a
    # fact by. `fsum1` says a one-term sum is its summand read at the limit,
    # so def:G's base clause reaches `a^0` where the definition says 1.
    'nn0absid', 'exp0',
    # A disequality is one fact in two orders and the corpus writes it as a
    # negated equation, which set.mm names and then commutes. `necom` alone
    # would not fit: it speaks of =/=, and `df-ne` is what relates that to
    # the -. = the `negates` line folds ≠ into.
    'df-ne', 'necom',
    # And a pair that cannot both hold because one of them does not:
    # `dvdslegcd` divides by anything but two zeros, and a natural number
    # is one of the two, so the pair is denied by denying its first half.
    'intnanrt',
]
