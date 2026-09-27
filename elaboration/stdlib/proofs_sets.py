"""Sets, for `proved.mm`.

What the library says of sets that set.mm says in more than one step:

- a part of a set is in its power set: `elpw2g` read one way by `biimpar`,
  closed so that `settle` may use it as a side condition's lemma;
- what is in the parts of X with a property: `elrab` over the power set,
  and `elpw2g` reading a member of the power set as a part, for
  `def:stdlib/sets/part-builder`;
- a finite set split into parts of one size m has (number of parts) · m
  elements, for `thm:stdlib/counting/partition-count`;
- a set of parts of a finite set is finite, for
  `thm:stdlib/counting/parts-finite`;
- a finite set and one in bijection with it have one size, for
  `thm:stdlib/counting/card-equal`.
"""

HEAD = """$( Sets: the parts of a set with a property, and a set counted by the
   equal parts it splits into. $)
$d x ps $.
$d x A $.
$d x B $.
$d v w y z K $.
$d v w y z X $.
$d v w y z M $.
$d v w y z ph $.
$d x y z $.

"""


def proofs(b):
    """(label, statement, proof[, hypotheses]) for each lemma."""
    return [part_in_power(b), part_member(b), partition_count(b),
            parts_finite(b), card_equal(b)]


def card_equal(b):
    """( ( A e. Fin /\\ A ~~ B ) -> ( # ` A ) = ( # ` B ) )

    B is finite as A is (`enfi`), and two finite sets in bijection have
    one size (`hashen`).
    """
    ph = b.wff('( A e. Fin /\\ A ~~ B )')
    finite = b.ap('simpl', {'ph': b.wff('A e. Fin'), 'ps': b.wff('A ~~ B')})
    paired = b.ap('simpr', {'ph': b.wff('A e. Fin'), 'ps': b.wff('A ~~ B')})
    other = b.ap('mpbid', {'ph': ph, 'ps': b.wff('A e. Fin'),
                           'ch': b.wff('B e. Fin')},
                 finite,
                 b.ap('syl', {'ph': ph, 'ps': b.wff('A ~~ B'),
                              'ch': b.wff('( A e. Fin <-> B e. Fin )')},
                      paired, b.ap('enfi', {'A': b.rpn('A'),
                                            'B': b.rpn('B')})))
    sizes = b.ap('syl2anc', {
        'ph': ph, 'ps': b.wff('A e. Fin'), 'ch': b.wff('B e. Fin'),
        'th': b.wff('( ( # ` A ) = ( # ` B ) <-> A ~~ B )')},
        finite, other, b.ap('hashen', {'A': b.rpn('A'), 'B': b.rpn('B')}))
    proof = b.ap('mpbird', {'ph': ph, 'ps': b.wff('( # ` A ) = ( # ` B )'),
                            'ch': b.wff('A ~~ B')}, paired, sizes)
    return ('gcardeq', '|- ( ( A e. Fin /\\ A ~~ B ) -> '
                       '( # ` A ) = ( # ` B ) )', proof)


def parts_finite(b):
    """( ph -> K e. Fin ), from X finite and every member of K a part of X.

    K is a part of the power set of X, which is finite (`pwfi`), so K is
    (`ssfi`).
    """
    ph = b.wff('ph')
    hyps = [('gpartsfin.1', '|- ( ph -> X e. Fin )'),
            ('gpartsfin.2', '|- ( ph -> A. y e. K y C_ X )')]
    for label, statement in hyps:
        b.hypothesis(label, statement)
    finite, within = (b.seq(label) for label, _s in hyps)
    each = b.ap('syl', {'ph': ph, 'ps': b.wff('A. y e. K y C_ X'),
                        'ch': b.wff('( y e. K -> y C_ X )')},
                within, b.ap('rsp', {'ph': b.wff('y C_ X'),
                                     'x': b.flabel['y'], 'A': b.rpn('K')}))
    in_power = b.ap('ssrdv', {'ph': ph, 'x': b.flabel['y'], 'A': b.rpn('K'),
                              'B': b.rpn('~P X')},
                    b.ap('syl6', {'ph': ph, 'ps': b.wff('y e. K'),
                                  'ch': b.wff('y C_ X'),
                                  'th': b.wff('y e. ~P X')},
                         each,
                         b.ap('biimpri', {'ph': b.wff('y e. ~P X'),
                                          'ps': b.wff('y C_ X')},
                              b.ap('velpw', {'x': b.flabel['y'],
                                             'A': b.rpn('X')}))))
    power_finite = b.ap('sylib', {'ph': ph, 'ps': b.wff('X e. Fin'),
                                  'ch': b.wff('~P X e. Fin')},
                        finite, b.ap('pwfi', {'A': b.rpn('X')}))
    proof = b.ap('syl2anc', {
        'ph': ph, 'ps': b.wff('~P X e. Fin'), 'ch': b.wff('K C_ ~P X'),
        'th': b.wff('K e. Fin')},
        power_finite, in_power, b.ap('ssfi', {'A': b.rpn('~P X'),
                                              'B': b.rpn('K')}))
    return ('gpartsfin', '|- ( ph -> K e. Fin )', proof, hyps)


def partition_count(b):
    """( ph -> ( # ` X ) = ( ( # ` K ) x. M ) ), from X finite, the members
    of K making up X, two of them that meet being equal, and each of size
    M in NN0.

    `hashiun` sums the sizes of a disjoint family of finite sets; the family
    is finite since it is a part of the power set of X (`pwfi`, `ssfi`), each
    member is finite as a part of X, and it is disjoint by `disjor` once "if
    Y and Z meet they are equal" is read as "Y = Z or they do not meet".
    `fsumconst` then counts a sum of M's.

    Each hypothesis binds letters of its own, w for the union and v for the
    sizes, so that a proof citing it answers each from a line spelt as that
    line is; `cbviunv` and `cbvralvw` bring them to y here.
    """
    ph = b.wff('ph')
    union = 'U_ y e. K y'
    meets = 'A. x e. ( y i^i z ) y = z'
    apart = '( y = z \\/ ( y i^i z ) = (/) )'
    hyps = [('gpartcnt.1', '|- ( ph -> X e. Fin )'),
            ('gpartcnt.2', '|- ( ph -> U_ w e. K w = X )'),
            ('gpartcnt.3', f'|- ( ph -> A. y e. K A. z e. K {meets} )'),
            ('gpartcnt.4', '|- ( ph -> A. v e. K ( # ` v ) = M )'),
            ('gpartcnt.5', '|- ( ph -> M e. NN0 )')]
    for label, statement in hyps:
        b.hypothesis(label, statement)
    finite, whole_w, pairs, sizes_v, m_nat = (b.seq(label)
                                              for label, _s in hyps)
    whole = b.ap('eqtr3id', {'ph': ph, 'A': b.rpn(union),
                             'B': b.rpn('U_ w e. K w'), 'C': b.rpn('X')},
                 b.ap('cbviunv', {'x': b.flabel['w'], 'y': b.flabel['y'],
                                  'A': b.rpn('K'), 'B': b.rpn('w'),
                                  'C': b.rpn('y')},
                      b.ap('id', {'ph': b.wff('w = y')})),
                 whole_w)
    sizes = b.ap('sylib', {
        'ph': ph, 'ps': b.wff('A. v e. K ( # ` v ) = M'),
        'ch': b.wff('A. y e. K ( # ` y ) = M')},
        sizes_v,
        b.ap('cbvralvw', {'x': b.flabel['v'], 'y': b.flabel['y'],
                          'A': b.rpn('K'), 'ph': b.wff('( # ` v ) = M'),
                          'ps': b.wff('( # ` y ) = M')},
             b.ap('eqeq1d', {'ph': b.wff('v = y'), 'A': b.rpn('( # ` v )'),
                             'B': b.rpn('( # ` y )'), 'C': b.rpn('M')},
                  b.ap('fveq2', {'A': b.rpn('v'), 'B': b.rpn('y'),
                                 'F': b.rpn('#')}))))
    at = b.wff('( ph /\\ y e. K )')

    # Each member is a part of X, so in its power set and finite.
    within = b.ap('sseqtrd', {'ph': at, 'A': b.rpn('y'), 'B': b.rpn(union),
                              'C': b.rpn('X')},
                  b.ap('adantl', {'ph': b.wff('y e. K'), 'ps': b.wff(
                      f'y C_ {union}'), 'ch': ph},
                       b.ap('ssiun2', {'x': b.flabel['y'], 'A': b.rpn('K'),
                                       'B': b.rpn('y')})),
                  b.ap('adantr', {'ph': ph, 'ps': b.wff(f'{union} = X'),
                                  'ch': b.wff('y e. K')}, whole))
    member_finite = b.ap('syl2anc', {
        'ph': at, 'ps': b.wff('X e. Fin'), 'ch': b.wff('y C_ X'),
        'th': b.wff('y e. Fin')},
        b.ap('adantr', {'ph': ph, 'ps': b.wff('X e. Fin'),
                        'ch': b.wff('y e. K')}, finite),
        within, b.ap('ssfi', {'A': b.rpn('X'), 'B': b.rpn('y')}))
    in_power = b.ap('ssrdv', {'ph': ph, 'x': b.flabel['y'], 'A': b.rpn('K'),
                              'B': b.rpn('~P X')},
                    b.ap('ex', {'ph': ph, 'ps': b.wff('y e. K'),
                                'ch': b.wff('y e. ~P X')},
                         b.ap('sylibr', {'ph': at, 'ps': b.wff('y C_ X'),
                                         'ch': b.wff('y e. ~P X')},
                              within,
                              b.ap('velpw', {'x': b.flabel['y'],
                                             'A': b.rpn('X')}))))
    power_finite = b.ap('sylib', {'ph': ph, 'ps': b.wff('X e. Fin'),
                                  'ch': b.wff('~P X e. Fin')},
                        finite, b.ap('pwfi', {'A': b.rpn('X')}))
    family_finite = b.ap('syl2anc', {
        'ph': ph, 'ps': b.wff('~P X e. Fin'), 'ch': b.wff('K C_ ~P X'),
        'th': b.wff('K e. Fin')},
        power_finite, in_power, b.ap('ssfi', {'A': b.rpn('~P X'),
                                              'B': b.rpn('K')}))

    # Two members sharing a point are equal: so equal, or with nothing in
    # common, since sharing none is the other case (`r19.3rzv`).
    meet = '( y i^i z )'
    shared = f'( {meet} =/= (/) -> y = z )'
    either = b.ap('3bitri', {
        'ph': b.wff(shared), 'ps': b.wff(f'( -. {meet} = (/) -> y = z )'),
        'ch': b.wff(f'( {meet} = (/) \\/ y = z )'), 'th': b.wff(apart)},
        b.ap('imbi1i', {'ph': b.wff(f'{meet} =/= (/)'),
                        'ps': b.wff(f'-. {meet} = (/)'),
                        'ch': b.wff('y = z')},
             b.ap('df-ne', {'A': b.rpn(meet), 'B': b.rpn('(/)')})),
        b.ap('pm4.64', {'ph': b.wff(f'{meet} = (/)'),
                        'ps': b.wff('y = z')}),
        b.ap('orcom', {'ph': b.wff(f'{meet} = (/)'),
                       'ps': b.wff('y = z')}))
    read = b.ap('syl', {'ph': b.wff(meets), 'ps': b.wff(shared),
                        'ch': b.wff(apart)},
                b.ap('com12', {'ph': b.wff(f'{meet} =/= (/)'),
                               'ps': b.wff(meets), 'ch': b.wff('y = z')},
                     b.ap('biimprd', {'ph': b.wff(f'{meet} =/= (/)'),
                                      'ps': b.wff('y = z'),
                                      'ch': b.wff(meets)},
                          b.ap('r19.3rzv', {'A': b.rpn(meet),
                                            'ph': b.wff('y = z'),
                                            'x': b.flabel['x']}))),
                b.ap('biimpi', {'ph': b.wff(shared), 'ps': b.wff(apart)},
                     either))
    every = b.ap('ralimi', {'ph': b.wff(f'A. z e. K {meets}'),
                            'ps': b.wff(f'A. z e. K {apart}'),
                            'x': b.flabel['y'], 'A': b.rpn('K')},
                 b.ap('ralimi', {'ph': b.wff(meets), 'ps': b.wff(apart),
                                 'x': b.flabel['z'], 'A': b.rpn('K')}, read))
    disjoint = b.ap('sylibr', {
        'ph': ph, 'ps': b.wff(f'A. y e. K A. z e. K {apart}'),
        'ch': b.wff('Disj_ y e. K y')},
        b.ap('syl', {'ph': ph,
                     'ps': b.wff(f'A. y e. K A. z e. K {meets}'),
                     'ch': b.wff(f'A. y e. K A. z e. K {apart}')},
             pairs, every),
        b.ap('disjor', {'i': b.flabel['y'], 'j': b.flabel['z'],
                        'A': b.rpn('K'), 'B': b.rpn('y'), 'C': b.rpn('z')},
             b.ap('id', {'ph': b.wff('y = z')})))

    # The count.
    summed = b.ap('hashiun', {'ph': ph, 'x': b.flabel['y'], 'A': b.rpn('K'),
                              'B': b.rpn('y')},
                  family_finite, member_finite, disjoint)
    size = f'( # ` {union} )'
    same_set = b.ap('fveq2d', {'ph': ph, 'A': b.rpn(union), 'B': b.rpn('X'),
                               'F': b.rpn('#')}, whole)
    each = b.ap('syl', {'ph': ph, 'ps': b.wff('A. y e. K ( # ` y ) = M'),
                        'ch': b.wff('sum_ y e. K ( # ` y ) = sum_ y e. K M')},
                sizes, b.ap('sumeq2', {'k': b.flabel['y'], 'A': b.rpn('K'),
                                       'B': b.rpn('( # ` y )'),
                                       'C': b.rpn('M')}))
    constant = b.ap('syl2anc', {
        'ph': ph, 'ps': b.wff('K e. Fin'), 'ch': b.wff('M e. CC'),
        'th': b.wff('sum_ y e. K M = ( ( # ` K ) x. M )')},
        family_finite, b.ap('nn0cnd', {'ph': ph, 'A': b.rpn('M')}, m_nat),
        b.ap('fsumconst', {'k': b.flabel['y'], 'A': b.rpn('K'),
                           'B': b.rpn('M')}))
    to_sum = b.ap('eqtr3d', {'ph': ph, 'A': b.rpn(size),
                             'B': b.rpn('( # ` X )'),
                             'C': b.rpn('sum_ y e. K ( # ` y )')},
                  same_set, summed)
    to_ms = b.ap('eqtrd', {'ph': ph, 'A': b.rpn('( # ` X )'),
                           'B': b.rpn('sum_ y e. K ( # ` y )'),
                           'C': b.rpn('sum_ y e. K M')}, to_sum, each)
    proof = b.ap('eqtrd', {'ph': ph, 'A': b.rpn('( # ` X )'),
                           'B': b.rpn('sum_ y e. K M'),
                           'C': b.rpn('( ( # ` K ) x. M )')}, to_ms, constant)
    return ('gpartcnt', '|- ( ph -> ( # ` X ) = ( ( # ` K ) x. M ) )', proof,
            hyps)


def part_in_power(b):
    """( ( B e. V /\\ A C_ B ) -> A e. ~P B )"""
    return ('gsspw', '|- ( ( B e. V /\\ A C_ B ) -> A e. ~P B )', b.ap(
        'biimpar', {'ph': b.wff('B e. V'), 'ps': b.wff('A e. ~P B'),
                    'ch': b.wff('A C_ B')},
        b.ap('elpw2g', {'A': b.rpn('A'), 'B': b.rpn('B'),
                        'V': b.rpn('V')})))


def part_member(b):
    """( B e. V -> ( A e. { x e. ~P B | ph } <-> ( A C_ B /\\ ps ) ) ),
    from ( x = A -> ( ph <-> ps ) )
    """
    at = ('gelrabpw.1', '|- ( x = A -> ( ph <-> ps ) )')
    b.hypothesis(*at)
    built = '{ x e. ~P B | ph }'
    member = f'A e. {built}'
    theirs = '( A e. ~P B /\\ ps )'
    ours = '( A C_ B /\\ ps )'
    elrab = b.ap('elrab', {'x': b.flabel['x'], 'A': b.rpn('A'),
                           'B': b.rpn('~P B'), 'ph': b.wff('ph'),
                           'ps': b.wff('ps')}, b.seq(at[0]))
    part = b.ap('anbi1d', {'ph': b.wff('B e. V'), 'ps': b.wff('A e. ~P B'),
                           'ch': b.wff('A C_ B'), 'th': b.wff('ps')},
                b.ap('elpw2g', {'A': b.rpn('A'), 'B': b.rpn('B'),
                                'V': b.rpn('V')}))
    proof = b.ap('bitrid', {'ph': b.wff(member), 'ps': b.wff(theirs),
                            'ch': b.wff('B e. V'), 'th': b.wff(ours)},
                 elrab, part)
    return ('gelrabpw', f'|- ( B e. V -> ( {member} <-> {ours} ) )', proof,
            [at])
