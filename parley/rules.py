"""The elaborator's rule tables: which set.mm lemma does each job.

This is the fourth of the elaborator's six parts (`ELABORATION.md`, "How the
elaborator is built"). It is data, not code. Given the shape of what is
wanted, a table names the set.mm lemma that answers it: which lemma lifts an
equation through each constructor, which carries a membership from one number
system to another or through an operation, what a closed numeral is, and the
spellings in which set.mm and the page say one thing two ways.

Growth goes here first. A pilot that meets a new difference between the page
and set.mm adds an entry, and `parley/labels.py` checks that every label here
is one set.mm has.

`MEMBERSHIP` says which set.mm lemmas an elaborator may lean on for what the
readable layer never writes. That a sum of integers is an integer, that an
integer is a real, that two integers may be multiplied either way round —
these are facts about set.mm's library rather than about the readable corpus,
and no field of a readable database is the place for them. They are one list
tried by matching, because they are one question: what does set.mm already
prove that says this?
"""
import field

# Which lemma rewrites a subterm, by what encloses it and which hole it
# sits in. The tree decides; nothing is searched for.
# A claim may change in more than one place at once — the claim of an
# induction holds its variable several times — so the lemma is chosen by
# which operands change together as well as by what encloses them.
CONGRUENCE = {
    ('co', (0,)): 'oveq1d', ('co', (1,)): 'oveq2d',
    ('co', (0, 1)): 'oveq12d',
    ('wbr', (0,)): 'breq1d', ('wbr', (1,)): 'breq2d',
    ('wbr', (0, 1)): 'breq12d',
    ('cfv', (0,)): 'fveq2d',
    ('wceq', (0,)): 'eqeq1d', ('wceq', (1,)): 'eqeq2d',
    ('wceq', (0, 1)): 'eqeq12d',
    ('wcel', (0,)): 'eleq1d', ('wcel', (1,)): 'eleq2d',
    ('wcel', (0, 1)): 'eleq12d',
    ('csu', (0,)): 'sumeq1d',
    ('cpw', (0,)): 'pweqd', ('csn', (0,)): 'sneqd', ('crn', (0,)): 'rneqd',
    ('cun', (0,)): 'uneq1d', ('cun', (1,)): 'uneq2d',
    ('cun', (0, 1)): 'uneq12d',
    ('cdif', (0,)): 'difeq1d', ('cdif', (1,)): 'difeq2d',
    ('cdif', (0, 1)): 'difeq12d',
    ('cin', (0,)): 'ineq1d', ('cin', (1,)): 'ineq2d',
    ('cin', (0, 1)): 'ineq12d',
    ('wss', (0,)): 'sseq1d', ('wss', (1,)): 'sseq2d',
    ('wss', (0, 1)): 'sseq12d',
    ('wa', (0,)): 'anbi1d', ('wa', (1,)): 'anbi2d',
    ('wa', (0, 1)): 'anbi12d',
    ('w3a', (0,)): '3anbi1d', ('w3a', (1,)): '3anbi2d',
    ('w3a', (2,)): '3anbi3d', ('w3a', (0, 1, 2)): '3anbi123d',
    ('wo', (0,)): 'orbi1d', ('wo', (1,)): 'orbi2d',
    ('wo', (0, 1)): 'orbi12d',
    ('wb', (0,)): 'bibi1d', ('wb', (1,)): 'bibi2d',
    ('wb', (0, 1)): 'bibi12d',
    ('wn', (0,)): 'notbid',
    # A universal over an `if ... then` changes both sides at once when
    # the name it binds stands on each of them.
    ('wi', (0,)): 'imbi1d', ('wi', (1,)): 'imbi2d',
    ('wi', (0, 1)): 'imbi12d',
    ('wral', (0,)): 'ralbidv', ('wrex', (0,)): 'rexbidv',
    # And the same over every set there is, which a `let X be a set`
    # quantifies and the subsets proof inducts under.
    ('wal', (0,)): 'albidv'}

# The constructors that take a function, operation or relation as an operand.
WRAPS = ('co', 'wbr', 'cfv')

# Lifting a closed biconditional through one level of a term. The
# deduction forms `congruence` uses take the scope as an antecedent;
# these take nothing, which is what a renaming needs.
RENAMED = {('wa', (0,)): 'anbi1i', ('wa', (1,)): 'anbi2i',
           ('wi', (0,)): 'imbi1i', ('wi', (1,)): 'imbi2i'}

# One binder: the lemma that changes what it binds over, and the one
# that changes the name it binds. Both closed, and the `w` on the
# second is set.mm's version that does not lean on ax-13.
BOUND = {'wrex': ('rexbii', 'cbvrexvw'),
         'wral': ('ralbii', 'cbvralvw'),
         'wal': ('albii', 'cbvalvw')}

# A class that binds a name, and the lemma that changes the name; its
# hypothesis says how the two bodies agree at x = y. None leans on ax-13. A
# map in a theorem the subsets proof cites binds `o` where the define it is
# compared with binds `l`, and those are one class; so are a defined sum's
# rule over `i` and the same sum a line writes over `j`.
CLASS_BOUND = {'cmpt': 'cbvmptv', 'crab': 'cbvrabv', 'csu': 'cbvsumv'}

# Stands where a join would name the constructor, for a biconditional a
# lemma states the other way round from the way a step reaches it. It is no
# label, so a statement built from it would not spell, which is what stops a
# second antecedent being folded past one read this way.
TURNED = 'the other way round'

# Which lemma discharges one thing a lemma asked, by how that thing was
# joined to what follows it and whether the lemma is still bare. The
# first is composed with the lemma itself; every later one is applied to
# what the last already deduced.
DISCHARGE = {
    ('wi', True): 'syl', ('wi', False): 'mpd',
    ('wb', True): 'sylib', ('wb', False): 'mpbid',
    (TURNED, True): 'sylibr', (TURNED, False): 'mpbird'}

# A claim `P → Q` from a biconditional between P and Q: the lemma taking
# it from left to right, then the one from right to left.
ONE_WAY = ('biimpd', 'biimprd')

# Instantiating a universal, by the binder: the lemma, the variable it
# names the domain by, and the domain where the binder names none. A
# restricted universal wants its term in the set it runs over, and an
# unrestricted one wants it only to be a set.
INSTANCES = {'wral': ('rspcv', 'B', None), 'wal': ('spcgv', 'V', 'cvv')}

# Which transitivity folds one link of a calculation into the run above
# it, by what each of the two claims is. Two relations in a row would
# want the transitivity of that relation and no chain writes one.
FOLDING = {
    ('wceq', 'wceq'): 'eqtrd', ('wceq', 'wbr'): 'eqbrtrd',
    ('wbr', 'wceq'): 'breqtrd'}

# A fact that conjoins several things says each of them, and the steps
# below cite them one at a time: an `obtain` hands over one body saying
# that q is positive, that x is p over q, and that nothing divides both.
SPLIT = {'wa': ('simpl', 'simpr'),
         'w3a': ('simp1', 'simp2', 'simp3')}
# And the other direction: what conjoins a proof of each part into a
# proof of the whole. `SPLIT` is read where a fact is taken apart and
# this where a goal is put together, and both are asked by label so
# that a shape neither names is left alone.
JOIN = {'wa': 'jca', 'w3a': '3jca'}

# What closes an induction, by the set the name inducted on runs over, and
# where that lemma starts. The two have the same six hypotheses in the same
# order and differ only in the set and the base, so choosing between them is
# choosing a label. Which one a proof wants is not the text's to say twice:
# `let n ∈ ℕ₀` already says it, and `starting at` is checked against it.
INDUCTION = {'cn': ('nnindd', 'c1'), 'cn0': ('nn0indd', 'cc0')}

# How set.mm names that a digit belongs to a number system, by the system.
# The label is the digit and this suffix throughout — `2z`, `1nn`, `0re` —
# so what a system needs here is how its name is spelt in that label and
# nothing else.
SYSTEMS = {'cc': 'cn', 'cr': 're', 'cz': 'z', 'cn': 'nn', 'cn0': 'nn0',
           'cq': 'q'}
# The lemma that puts a sum, difference, product or power in a number system
# from its parts being there, by operator and system; a power's exponent is
# in ℕ₀ whatever the system. A compound's membership is built from its
# atoms' this way, so an atom's is the step's own line where it wrote one.
CLOSED = {
    ('caddc', 'cc'): 'addcld', ('cmin', 'cc'): 'subcld',
    ('cmul', 'cc'): 'mulcld', ('cexp', 'cc'): 'expcld',
    ('caddc', 'cr'): 'readdcld', ('cmin', 'cr'): 'resubcld',
    ('cmul', 'cr'): 'remulcld', ('cexp', 'cr'): 'reexpcld',
    ('caddc', 'cz'): 'zaddcld', ('cmin', 'cz'): 'zsubcld',
    ('cmul', 'cz'): 'zmulcld', ('cexp', 'cz'): 'zexpcld',
    ('caddc', 'cn'): 'nnaddcld', ('cmul', 'cn'): 'nnmulcld',
    ('caddc', 'cn0'): 'nn0addcld', ('cmul', 'cn0'): 'nn0mulcld',
    ('cexp', 'cn0'): 'nn0expcld',
}
NEGATED = {'cc': 'negcld', 'cr': 'renegcld', 'cz': 'znegcld'}
# A quotient asks a third thing of its parts, that the divisor is not zero,
# so it is closed only where the caller says how that is shown.
DIVIDED = {'cc': 'divcld', 'cr': 'redivcld'}

# Which number sets lie inside which, each with the lemma saying so of a
# member (`SYNTAX.md`: a line said of every member of a set says it of every
# member of a set inside that one). One table, read by the checker and the
# elaborator alike, and declared rather than searched.
SYSTEM_OF = {'ℕ': 'cn', 'ℕ₀': 'cn0', 'ℤ': 'cz', 'ℚ': 'cq', 'ℝ': 'cr',
             'ℂ': 'cc'}
WITHIN = {
    'cn': {'cn0': 'nnnn0', 'cz': 'nnz', 'cq': 'nnq', 'cr': 'nnre',
           'cc': 'nncn'},
    'cn0': {'cz': 'nn0z', 'cr': 'nn0re', 'cc': 'nn0cn'},
    'cz': {'cq': 'zq', 'cr': 'zre', 'cc': 'zcn'},
    'cq': {'cr': 'qre', 'cc': 'qcn'},
    'cr': {'cc': 'recn'},
}
# What else a membership says of its term, as the page writes it with x for
# the term, and the lemma that says it (`SYNTAX.md`, what a membership line
# says).
IMPLIED = {'cn': (('x ≥ 1', 'nnge1'), ('x ≠ 0', 'nnne0')),
           'cn0': (('x ≥ 0', 'nn0ge0'),)}

# A range lies inside ℕ from 1 and ℕ₀ from 0, and inside ℤ from anywhere.
# (the system, the numeral it must start at or None, the lemma)
RANGE_WITHIN = (('cn', 'c1', 'elfznn'), ('cn0', 'cc0', 'elfznn0'),
                ('cz', None, 'elfzelz'))


def within_path(small, big):
    """The lemmas carrying a member of `small` into `big`, by labels, in
    order; [] where the two are one; None where the table does not put
    `small` inside `big`. A direct entry is taken over a longer way: set.mm
    says ℕ ⊆ ℝ as `nnre`, and ℕ₀ ⊆ ℚ only by way of ℤ.
    """
    if small == big:
        return []
    direct = WITHIN.get(small, {}).get(big)
    if direct is not None:
        return [direct]
    for middle, lemma in WITHIN.get(small, {}).items():
        rest = within_path(middle, big)
        if rest is not None:
            return [lemma, *rest]
    return None

# What a term built from numerals alone is spelt with: the digits, the
# decimal that joins them, and the operations `arithmetic` reads.
NUMERIC = frozenset({
    *field.DIGITS, 'cdc', 'co', 'caddc', 'cmin', 'cmul', 'cdiv', 'cexp',
    'cneg'})

# A whole number set.mm writes in ℕ₀ is in these by the closed lemma
# each names, which asks the number's own fact and not one in a scope.
FROM_NN0 = {'cn0': None, 'cz': 'nn0zi', 'cr': 'nn0rei',
            'cc': 'nn0cni'}

# The lemma that makes a term a set, in set.mm's sense of not a proper
# class, by the constructor at its head; what it asks is its parts' sethood,
# which the same table answers. A kernel variable is a set by `vex`, and a
# class the statement introduced by its `let` line (`sethood@` in `run`).
# `READERS.md`: this is apparatus, and the page never writes it.
SETHOOD = {'cpw': 'pwexg', 'cdif': 'difexg', 'cun': 'unexg', 'csn': 'snex',
           'crn': 'rnexg', 'cmpt': 'mptexg', 'crab': 'rabexg', 'c0': '0ex',
           'cv': 'vex', 'co': 'ovex', 'cif': 'ifexg', 'cn': 'nnex',
           'cn0': 'nn0ex', 'csu': 'sumex'}

# Two differences against zero added, by which of the two is strictly
# below it: the lemma that adds them and keeps the strictness.
ADDING = {(True, False): 'ltleadd', (False, True): 'leltadd',
          (True, True): 'lt2add'}

# A denied `<` or `≤` said the other way round, by the relation denied:
# that relation's label, the one that holds instead, and the lemma saying
# the two are the same.
DENIED = {'<': ('clt', 'cle', 'lenlt'), '<=': ('cle', 'clt', 'ltnle')}

# What says a thing lies in a class, by where that class stands among its
# parts: a membership, and a map's codomain. Where a map's values land is
# the same kind of question as where a set lives, and set.mm asks it the
# same way: `f1f1orn` wants a codomain and says nothing about it, because
# being one-to-one into one class is being one-to-one into any that holds
# the values. A class a lemma asks for here and nothing fixes is `_V`,
# which holds them all (`sethood` in `parley/matcher.py`).
HELD_IN = {'wcel': 1, 'wf': 1, 'wf1': 1, 'wfo': 1, 'wf1o': 1}

# The operations a method combining atoms looks inside, and the
# connectives and relations between the terms of the claim it proves.
ARITHMETIC = frozenset({'caddc', 'cmin', 'cmul', 'cdiv'})
RELATIONS = frozenset({'wceq', 'wne', 'wbr', 'wn', 'wa'})

# The rules that put a statement in one standard form, so that what a lemma
# says and what is wanted can be compared as they stand: each a set.mm
# biconditional or equation, by which of its two sides is the standard one,
# `LEFT` or `RIGHT`. A rule rewrites only toward a side whose
# variables all appear on the other, so rewriting ends and has one answer:
# `rexss` rewrites the page's restriction in the body back to set.mm's
# restriction in the domain, because the other way would have to invent the
# larger set. What a rule asks — `rexss` a subset, `exp0` a complex number —
# is settled where it is applied.
LEFT, RIGHT = 0, 1           # a two-sided statement's sides, as children
STANDARD = {'df-3or': RIGHT, 'df-ne': RIGHT, 'ralrp': RIGHT, 'rexrp': RIGHT,
            'exp0': RIGHT, 'nn0absid': RIGHT, 'rexss': LEFT,
            'rextru': RIGHT}

# The rules whose two sides are the same shape the other way round, which no
# direction can orient: the two sides are put in a fixed order instead, the
# one whose reverse Polish sorts first on the left. Inequalities are never
# among them, since their sides are not interchangeable.
SYMMETRIC = ('eqcom', 'addcom', 'mulcom')

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
    # A numeral of more than one digit, set.mm's decimal `; A B`, is not
    # among these: `elaborate.decimal_within` builds its membership from
    # its digits, because `deccl` asks its parts as closed facts and a
    # search proves everything under the step's scope.
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
    # A sum asks that its range be finite and that each of its terms be a
    # number, and a term is often a function's value at the index: a digit
    # d(k) is an integer because d maps into ℤ, and 10^k because 10 is one
    # and k is in ℕ₀.
    'fzfi', 'ffvelcdm', 'zexpcl',
    # A binomial coefficient is a whole number at every integer, and a
    # power's exponent n − k is a whole number when k is in 0 … n, which is
    # the range the binomial sum runs over.
    'bccl', 'fznn0sub',
    # and an index of a sum to m is in the range to m + 1, where the
    # exponent (m + 1) − k is a whole number: the binomial step's terms
    # carry that exponent while their sum still runs to m.
    'fzelp1',
    # An index of a sum from 1 is a natural number, where a power wants it.
    'elfznn',
    # set.mm says a coefficient is zero when k < 0 or n < k, as one
    # disjunction, and a proof says which of the two holds. A line saying
    # one side is the disjunction, which the page never writes.
    'olc', 'orc',
    'addcl', 'subcl', 'mulcl', 'sqcl', 'readdcl', 'remulcl', 'resqcl',
    'renegcl', 'negcl', 'reexpcl', 'nn0expcl', '2nn0', 'peano2nn0',
    # and what a commuting pair asks, which `db/notation.records` declares by
    # notation and this answers by statement
    'mulcom', 'addcom',
    # Sethood, which set theory asks where arithmetic asks closure, is not
    # among these: `elaborate.made_a_set` reads it off the constructor at a
    # term's head (`SETHOOD`), and a name the page introduces is a
    # set by the way it was introduced. No proof here needs a subset of a set
    # to be a set; one that does fails at its step, which is where `ssexg`
    # would be added, with that step as its test.
    #
    # A singleton holds what it names, which `elpwg`'s users ask.
    'snidg',
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
    # and what an order relation asks, which is the same kind of thing.
    # `nn0p1gt0` is what a size given as k + 1 says about being positive,
    # which `hashgt0elex` asks before it will say the set has an element.
    'ltle', 'ltnri', 'leid', 'nn0ge0', 'nngt0', 'nn0p1gt0',
    # A lemma stated over the integers asks what a natural number being one
    # does not say in those words: `divalg` divides by anything but zero,
    # and the readable statement divides by a natural number. It bounds by
    # the absolute value for the same reason, which over ℕ₀ is no bound at
    # all.
    'nnne0',
    # The two equations in this list, and what `said_otherwise` rewrites a
    # fact by. `fsum1` says a one-term sum is its summand read at the limit,
    # so a sum of powers from 0 to 0 reaches `a^0` where a line may say 1.
    'nn0absid', 'exp0',
    # A disequality is one fact in two orders and the corpus writes it as a
    # negated equation, which set.mm names and then commutes. `necom` alone
    # would not fit: it speaks of =/=, and `df-ne` is what relates that to
    # the -. = the `negates` line folds ≠ into.
    'df-ne', 'necom',
    # A continuous function's domain and codomain lie in ℂ, which
    # `elcncf2` asks before it says what continuity is, and which a reader
    # told f is continuous on [a, b] is never told. The line saying it is
    # continuous is what says so.
    'cncfrss', 'cncfrss2',
    # And a pair that cannot both hold because one of them does not:
    # `dvdslegcd` divides by anything but two zeros, and a natural number
    # is one of the two, so the pair is denied by denying its first half.
    'intnanrt',
]
