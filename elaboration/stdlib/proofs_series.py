"""The value of a series, for `proved.mm`.

The readable layer says a series is the limit of its partial sums: the
partial sums Σ(k = 1 to n) t(k) tend to L, so Σ(k = 1 to ∞) t(k) = L. set.mm
defines an infinite sum through a sequence of its own (`seq`), and no single
label says the readable form. `sersumlim` is it, from three that together
do: a sequence that tends to something converges (`releldmi`, `climrel`);
the partial sums of a convergent series tend to its sum (`isumclim3`); and
a sequence has one limit (`climuni`).

It is stated as a deduction, as set.mm states its series lemmas:
`isumclim3` forbids the index in what the statement assumes, and the
partial sums bind it.

The page defines a limit the way a textbook does: however small a positive
ε, there is a natural number N such that every term after the N-th is
within ε of the limit. set.mm's `clim2` says it over
ℝ⁺, over an upper integer set, and with each term complex, and it names
its index apart from the map's, so it cannot read a sequence written as a
map. `climnnre` is the page's form. `rlimclim` and `rlim2` give the limit
of a map over ℕ in the real sense, `ralrp` moves ε from ℝ⁺ to ℝ, and
`rexuzre` moves N from ℝ to ℕ.
"""

HEAD = """$( Series: the limit of a sequence as the page defines it, and the value
   of a series as the limit of its partial sums. $)
$d j k n $.
$d A j n x $.
$d B j x $.
$d ph j k n x $.

"""


def proofs(b):
    """(label, statement, proof, hypotheses) for each lemma."""
    return [limit(b), series(b)]


def limit(b):
    """`climnnre`: a real sequence on ℕ tends to a real A exactly when, for
    every positive x, some j ∈ ℕ has every later term within x of A.
    """
    f = '( n e. NN |-> B )'
    near = '( abs ` ( B - A ) ) < x'
    tail = f'A. n e. NN ( j <_ n -> {near} )'
    upper = f'A. n e. ( ZZ>= ` j ) {near}'
    real = ('climnnre.1', '|- ( ( ph /\\ n e. NN ) -> B e. RR )')
    limit_real = ('climnnre.2', '|- ( ph -> A e. RR )')
    for label, statement in (real, limit_real):
        b.hypothesis(label, statement)
    v = b.flabel
    ph = b.wff('ph')
    at_n = b.wff('( ph /\\ n e. NN )')

    # The terms are complex, so the map is a sequence of complex numbers.
    term = b.ap('recnd', {'ph': at_n, 'A': b.rpn('B')}, b.seq(real[0]))
    to_cc = b.ap('fmptd', {'ph': ph, 'x': v['n'], 'A': b.rpn('NN'),
                           'B': b.rpn('B'), 'C': b.rpn('CC'),
                           'F': b.rpn(f)},
                 term, b.ap('eqid', {'A': b.rpn(f)}))

    # On ℕ, which is an upper integer set, the two senses of limit agree,
    # and the real sense has an ε form for a map.
    one_z = b.ap('a1i', {'ph': b.wff('1 e. ZZ'), 'ps': ph}, b.seq('1z'))
    senses = b.ap('rlimclim', {'ph': ph, 'A': b.rpn('A'), 'F': b.rpn(f),
                               'M': b.rpn('1'), 'Z': b.rpn('NN')},
                  b.seq('nnuz'), one_z, to_cc)
    q_rr = f'E. j e. RR {tail}'
    q_nn = f'E. j e. NN {tail}'
    eps = b.ap('rlim2', {'ph': ph, 'x': v['x'], 'y': v['j'], 'z': v['n'],
                         'A': b.rpn('NN'), 'B': b.rpn('B'),
                         'C': b.rpn('A')},
               b.ap('ralrimiva', {'ph': ph, 'ps': b.wff('B e. CC'),
                                  'x': v['n'], 'A': b.rpn('NN')}, term),
               b.ap('a1i', {'ph': b.wff('NN C_ RR'), 'ps': ph},
                    b.seq('nnssre')),
               b.ap('recnd', {'ph': ph, 'A': b.rpn('A')},
                    b.seq(limit_real[0])))
    plus = f'A. x e. RR+ {q_rr}'
    tends = f'{f} ~~> A'
    first = b.ap('bitr3d', {'ph': ph, 'ps': b.wff(f'{f} ~~>r A'),
                            'ch': b.wff(tends), 'th': b.wff(plus)},
                 senses, eps)
    over_rr = f'A. x e. RR ( 0 < x -> {q_rr} )'
    second = b.ap('bitrdi', {'ph': ph, 'ps': b.wff(tends),
                             'ch': b.wff(plus), 'th': b.wff(over_rr)},
                  first, b.ap('ralrp', {'ph': b.wff(q_rr), 'x': v['x']}))

    # Past some real is past some natural number: for j ∈ ℕ, being in the
    # upper integers from j is, among the natural numbers, being at least j.
    within = b.ap('syl', {'ph': b.wff('j e. NN'),
                          'ps': b.wff('( ZZ>= ` j ) C_ NN'),
                          'ch': b.wff(f'( {upper} <-> A. n e. NN ( n e. '
                                      f'( ZZ>= ` j ) -> {near} ) )')},
                  b.ap('uznnssnn', {'N': b.rpn('j')}),
                  b.ap('ralss', {'ph': b.wff(near), 'x': v['n'],
                                 'A': b.rpn('( ZZ>= ` j )'),
                                 'B': b.rpn('NN')}))
    both = b.wff('( j e. NN /\\ n e. NN )')
    ints = b.ap('anim12i', {'ph': b.wff('j e. NN'), 'ps': b.wff('j e. ZZ'),
                            'ch': b.wff('n e. NN'), 'th': b.wff('n e. ZZ')},
                b.ap('nnz', {'N': b.rpn('j')}),
                b.ap('nnz', {'N': b.rpn('n')}))
    at_least = b.ap('syl', {'ph': both,
                            'ps': b.wff('( j e. ZZ /\\ n e. ZZ )'),
                            'ch': b.wff('( n e. ( ZZ>= ` j ) <-> j <_ n )')},
                    ints, b.ap('eluz', {'M': b.rpn('j'), 'N': b.rpn('n')}))
    each = b.ap('imbi1d', {'ph': both,
                           'ps': b.wff('n e. ( ZZ>= ` j )'),
                           'ch': b.wff('j <_ n'), 'th': b.wff(near)},
                at_least)
    among = b.ap('ralbidva', {'ph': b.wff('j e. NN'),
                              'ps': b.wff(f'( n e. ( ZZ>= ` j ) -> {near} )'),
                              'ch': b.wff(f'( j <_ n -> {near} )'),
                              'x': v['n'], 'A': b.rpn('NN')}, each)
    per_j = b.ap('bitrd', {'ph': b.wff('j e. NN'), 'ps': b.wff(upper),
                           'ch': b.wff(f'A. n e. NN ( n e. ( ZZ>= ` j ) '
                                       f'-> {near} )'),
                           'th': b.wff(tail)},
                 within, among)
    by_nn = b.ap('rexbiia', {'ph': b.wff(upper), 'ps': b.wff(tail),
                             'x': v['j'], 'A': b.rpn('NN')}, per_j)
    by_rr = b.ap('ax-mp', {'ph': b.wff('1 e. ZZ'),
                           'ps': b.wff(f'( E. j e. NN {upper} <-> {q_rr} )')},
                 b.seq('1z'),
                 b.ap('rexuzre', {'ph': b.wff(near), 'j': v['j'],
                                  'k': v['n'], 'M': b.rpn('1'),
                                  'Z': b.rpn('NN')},
                      b.seq('nnuz')))
    moved = b.ap('bitr3i', {'ph': b.wff(q_rr),
                            'ps': b.wff(f'E. j e. NN {upper}'),
                            'ch': b.wff(q_nn)},
                 by_rr, by_nn)
    over_nn = f'A. x e. RR ( 0 < x -> {q_nn} )'
    lifted = b.ap('ralbii', {'ph': b.wff(f'( 0 < x -> {q_rr} )'),
                             'ps': b.wff(f'( 0 < x -> {q_nn} )'),
                             'x': v['x'], 'A': b.rpn('RR')},
                  b.ap('imbi2i', {'ph': b.wff(q_rr), 'ps': b.wff(q_nn),
                                  'ch': b.wff('0 < x')}, moved))
    proof = b.ap('bitrdi', {'ph': ph, 'ps': b.wff(tends),
                            'ch': b.wff(over_rr), 'th': b.wff(over_nn)},
                 second, lifted)
    return ('climnnre', f'|- ( ph -> ( {tends} <-> {over_nn} ) )', proof,
            [real, limit_real])


def series(b):
    """(label, statement, proof, hypotheses) for `sersumlim`."""
    g = '( n e. NN |-> sum_ k e. ( 1 ... n ) A )'
    z = '( ZZ>= ` 1 )'
    s = f'sum_ k e. {z} A'
    real = ('sersumlim.1', '|- ( ( ph /\\ k e. NN ) -> A e. RR )')
    tends = ('sersumlim.2', f'|- ( ph -> {g} ~~> B )')
    for label, statement in (real, tends):
        b.hypothesis(label, statement)
    v = b.flabel
    ph = b.wff('ph')

    # The partial sums converge, since they tend to B.
    conv = b.seq(tends[0])
    dom = b.ap('syl', {'ph': ph, 'ps': b.wff(f'{g} ~~> B'),
                       'ch': b.wff(f'{g} e. dom ~~>')},
               conv,
               b.ap('releldmi', {'A': b.rpn(g), 'B': b.rpn('B'),
                                 'R': b.rpn('~~>')},
                    b.seq('climrel')))

    def natural(name):
        """( ( ph /\\ name e. Z ) -> name e. NN ), since Z is ℕ."""
        under = f'( ph /\\ {name} e. {z} )'
        return b.ap('eleqtrrdi', {'ph': b.wff(under), 'A': b.rpn(name),
                                  'B': b.rpn(z), 'C': b.rpn('NN')},
                    b.ap('simpr', {'ph': ph, 'ps': b.wff(f'{name} e. {z}')}),
                    b.seq('nnuz'))

    # Each term is complex, from the first hypothesis.
    at_k = f'( ph /\\ k e. {z} )'
    term = b.ap('syl', {'ph': b.wff(at_k), 'ps': b.wff('A e. RR'),
                        'ch': b.wff('A e. CC')},
                b.ap('syl', {'ph': b.wff(at_k),
                             'ps': b.wff('( ph /\\ k e. NN )'),
                             'ch': b.wff('A e. RR')},
                     b.ap('jca', {'ph': b.wff(at_k), 'ps': ph,
                                  'ch': b.wff('k e. NN')},
                          b.ap('simpl', {'ph': ph,
                                         'ps': b.wff(f'k e. {z}')}),
                          natural('k')),
                     b.seq(real[0])),
                b.ap('recn', {'A': b.rpn('A')}))

    # The j-th partial sum is the sum to j, by the map's own rule.
    at_j = f'( ph /\\ j e. {z} )'
    upto_n, upto_j = 'sum_ k e. ( 1 ... n ) A', 'sum_ k e. ( 1 ... j ) A'
    moved = b.ap('syl', {'ph': b.wff('n = j'),
                         'ps': b.wff('( 1 ... n ) = ( 1 ... j )'),
                         'ch': b.wff(f'{upto_n} = {upto_j}')},
                 b.ap('oveq2', {'A': b.rpn('n'), 'B': b.rpn('j'),
                                'C': b.rpn('1'), 'F': b.rpn('...')}),
                 b.ap('sumeq1', {'A': b.rpn('( 1 ... n )'),
                                 'B': b.rpn('( 1 ... j )'), 'C': b.rpn('A'),
                                 'k': v['k']}))
    value = b.ap('fvmptd3', {'ph': b.wff(at_j), 'x': v['n'], 'A': b.rpn('j'),
                             'B': b.rpn(upto_n), 'C': b.rpn(upto_j),
                             'D': b.rpn('NN'), 'F': b.rpn(g),
                             'V': b.rpn('_V')},
                 b.ap('eqid', {'A': b.rpn(g)}),
                 moved,
                 natural('j'),
                 b.ap('a1i', {'ph': b.wff(f'{upto_j} e. _V'),
                              'ps': b.wff(at_j)},
                      b.ap('sumex', {'A': b.rpn('( 1 ... j )'),
                                     'B': b.rpn('A'), 'k': v['k']})))

    # So the partial sums tend to the sum as well, and to B, and those are
    # one limit.
    to_sum = b.ap('isumclim3', {'ph': ph, 'A': b.rpn('A'), 'j': v['j'],
                                'k': v['k'], 'F': b.rpn(g), 'M': b.rpn('1'),
                                'Z': b.rpn(z)},
                  b.ap('eqid', {'A': b.rpn(z)}),
                  b.ap('a1i', {'ph': b.wff('1 e. ZZ'), 'ps': ph},
                       b.seq('1z')),
                  dom, term, value)
    one = b.ap('syl', {'ph': ph, 'ps': b.wff(f'( {g} ~~> B /\\ {g} ~~> {s} )'),
                       'ch': b.wff(f'B = {s}')},
               b.ap('jca', {'ph': ph, 'ps': b.wff(f'{g} ~~> B'),
                            'ch': b.wff(f'{g} ~~> {s}')},
                    conv, to_sum),
               b.ap('climuni', {'A': b.rpn('B'), 'B': b.rpn(s),
                                'F': b.rpn(g)}))
    proof = b.ap('eqcomd', {'ph': ph, 'A': b.rpn('B'), 'B': b.rpn(s)}, one)
    return ('sersumlim', f'|- ( ph -> {s} = B )', proof, [real, tends])
