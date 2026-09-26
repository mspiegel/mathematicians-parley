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
"""

HEAD = """$( Series: the value of a series is the limit of its partial sums. $)
$d j k n $.
$d A j n $.
$d ph j k $.

"""


def proofs(b):
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
    return [('sersumlim', f'|- ( ph -> {s} = B )', proof, [real, tends])]
