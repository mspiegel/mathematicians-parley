"""Groups, for `proved.mm`.

What Lagrange's theorem asks of a group that set.mm says in several steps:

- what is in a coset gH: set.mm's coset is the sum of the subsets {g} and H
  (`LSSum`), and `lsmelvalx` says its members are the y·z with y ∈ {g} and
  z ∈ H, which `rexsng` reads as the g·z with z ∈ H, for
  `def:stdlib/groups/coset`.
"""

HEAD = """$( Groups: what is in a coset. $)
$d y z A $.
$d y z S $.
$d y z X $.
$d y z G $.

"""


def proofs(b):
    """(label, statement, proof[, hypotheses]) for each lemma."""
    return [coset_member(b)]


def coset_member(b):
    """( ( G e. Grp /\\ S C_ ( Base ` G ) /\\ A e. ( Base ` G ) ) ->
    ( X e. ( { A } ( LSSum ` G ) S ) <-> E. z e. S X = ( A ( +g ` G ) z ) ) )
    """
    base, plus, sums = '( Base ` G )', '( +g ` G )', '( LSSum ` G )'
    held = f'( G e. Grp /\\ S C_ {base} /\\ A e. {base} )'
    member = f'X e. ( {{ A }} {sums} S )'
    pairs = f'E. y e. {{ A }} E. z e. S X = ( y {plus} z )'
    ours = f'E. z e. S X = ( A {plus} z )'
    parts = {'ph': b.wff('G e. Grp'), 'ps': b.wff(f'S C_ {base}'),
             'ch': b.wff(f'A e. {base}')}
    asked = f'( G e. _V /\\ {{ A }} C_ {base} /\\ S C_ {base} )'
    # What lsmelvalx asks, from what the lemma is given.
    set_g = b.ap('syl', {'ph': b.wff(held), 'ps': b.wff('G e. Grp'),
                         'ch': b.wff('G e. _V')},
                 b.ap('simp1', parts),
                 b.ap('elex', {'A': b.rpn('G'), 'B': b.rpn('Grp')}))
    single = b.ap('syl', {'ph': b.wff(held), 'ps': b.wff(f'A e. {base}'),
                          'ch': b.wff(f'{{ A }} C_ {base}')},
                  b.ap('simp3', parts),
                  b.ap('snssi', {'A': b.rpn('A'), 'B': b.rpn(base)}))
    asks = b.ap('3jca', {'ph': b.wff(held), 'ps': b.wff('G e. _V'),
                         'ch': b.wff(f'{{ A }} C_ {base}'),
                         'th': b.wff(f'S C_ {base}')},
                set_g, single, b.ap('simp2', parts))
    summed = b.ap('lsmelvalx', {'G': b.rpn('G'), 'V': b.rpn('_V'),
                                'T': b.rpn('{ A }'), 'U': b.rpn('S'),
                                'B': b.rpn(base), 'X': b.rpn('X'),
                                '.+': b.rpn(plus), '.(+)': b.rpn(sums),
                                'y': b.flabel['y'], 'z': b.flabel['z']},
                  b.ap('eqid', {'A': b.rpn(base)}),
                  b.ap('eqid', {'A': b.rpn(plus)}),
                  b.ap('eqid', {'A': b.rpn(sums)}))
    first = b.ap('syl', {'ph': b.wff(held), 'ps': b.wff(asked),
                         'ch': b.wff(f'( {member} <-> {pairs} )')},
                 asks, summed)
    # The singleton's one member is A.
    at_a = b.ap('rexbidv', {'ph': b.wff('y = A'),
                            'ps': b.wff(f'X = ( y {plus} z )'),
                            'ch': b.wff(f'X = ( A {plus} z )'),
                            'x': b.flabel['z'], 'A': b.rpn('S')},
                b.ap('eqeq2d', {'ph': b.wff('y = A'),
                                'A': b.rpn(f'( y {plus} z )'),
                                'B': b.rpn(f'( A {plus} z )'),
                                'C': b.rpn('X')},
                     b.ap('oveq1', {'A': b.rpn('y'), 'B': b.rpn('A'),
                                    'C': b.rpn('z'), 'F': b.rpn(plus)})))
    single_out = b.ap('rexsng', {'x': b.flabel['y'], 'A': b.rpn('A'),
                                 'V': b.rpn(base),
                                 'ph': b.wff(f'E. z e. S X = ( y {plus} z )'),
                                 'ps': b.wff(ours)}, at_a)
    second = b.ap('syl', {'ph': b.wff(held), 'ps': b.wff(f'A e. {base}'),
                          'ch': b.wff(f'( {pairs} <-> {ours} )')},
                  b.ap('simp3', parts), single_out)
    return ('gelcoset', f'|- ( {held} -> ( {member} <-> {ours} ) )', b.ap(
        'bitrd', {'ph': b.wff(held), 'ps': b.wff(member),
                  'ch': b.wff(pairs), 'th': b.wff(ours)}, first, second))
