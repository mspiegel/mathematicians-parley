"""Functions and their images, for `proved.mm`.

What Schröder–Bernstein asks of functions that set.mm says in two steps and
the page in one. Each lemma is a chain of two or three set.mm lemmas:

- a bigger set has a bigger image: `mptss` widens the map and `rnss` its
  range, for `thm:stdlib/functions/image-monotone`;
- a one-to-one function's inverse undoes it: `f1f1orn` makes it a bijection
  onto its range, where `f1ocnvfv1` applies, for
  `thm:stdlib/functions/inverse-value`;
- a function that is one-to-one and reaches every point is a bijection:
  `dffo3` reads the reaching as onto, `df-f1o` puts the two together, and
  `f1oeng` gives the bijection, for `thm:stdlib/functions/onto-bijection`;
- a map sends its domain into a set exactly when each value lies there:
  `fmpt` says it of a name for the map, and `eqid` names the map itself,
  for `thm:stdlib/functions/function-into`;
- a value lies in the image: `elrnmpt1s` with the map named by `eqid`,
  the value at the point by `fveq2`, and that value a set by `fvex`, for
  `thm:stdlib/functions/value-in-image`.
"""

HEAD = """$( Functions: images, inverses, and a bijection from one-to-one and
   onto. $)
$d x y A $.
$d x y B $.
$d x y F $.
$d x D $.

"""


def proofs(b):
    """(label, statement, proof) for each lemma."""
    return [image_monotone(b), inverse_value(b), onto_bijection(b),
            map_into(b), value_in_image(b)]


def value_in_image(b):
    """( D e. A -> ( F ` D ) e. ran ( x e. A |-> ( F ` x ) ) )"""
    mapped = '( x e. A |-> ( F ` x ) )'
    value = '( F ` D )'
    both = b.ap('elrnmpt1s', {'x': b.flabel['x'], 'A': b.rpn('A'),
                              'B': b.rpn('( F ` x )'), 'C': b.rpn(value),
                              'D': b.rpn('D'), 'F': b.rpn(mapped),
                              'V': b.rpn('_V')},
                b.ap('eqid', {'A': b.rpn(mapped)}),
                b.ap('fveq2', {'A': b.rpn('x'), 'B': b.rpn('D'),
                               'F': b.rpn('F')}))
    return ('gfvrnmpt', f'|- ( D e. A -> {value} e. ran {mapped} )', b.ap(
        'mpan2', {'ph': b.wff('D e. A'), 'ps': b.wff(f'{value} e. _V'),
                  'ch': b.wff(f'{value} e. ran {mapped}')},
        b.ap('fvex', {'F': b.rpn('F'), 'A': b.rpn('D')}), both))


def map_into(b):
    """( A. x e. A C e. B <-> ( x e. A |-> C ) : A --> B )"""
    mapped = '( x e. A |-> C )'
    return ('gfmpt', f'|- ( A. x e. A C e. B <-> {mapped} : A --> B )',
            b.ap('fmpt', {'x': b.flabel['x'], 'A': b.rpn('A'),
                          'C': b.rpn('C'), 'B': b.rpn('B'),
                          'F': b.rpn(mapped)},
                 b.ap('eqid', {'A': b.rpn(mapped)})))


def image_monotone(b):
    """( A C_ B -> ran ( x e. A |-> C ) C_ ran ( x e. B |-> C ) )"""
    small, large = '( x e. A |-> C )', '( x e. B |-> C )'
    says = f'ran {small} C_ ran {large}'
    return ('grnmptss', f'|- ( A C_ B -> {says} )', b.ap(
        'syl', {'ph': b.wff('A C_ B'), 'ps': b.wff(f'{small} C_ {large}'),
                'ch': b.wff(says)},
        b.ap('mptss', {'A': b.rpn('A'), 'B': b.rpn('B'), 'x': b.flabel['x'],
                       'C': b.rpn('C')}),
        b.ap('rnss', {'A': b.rpn(small), 'B': b.rpn(large)})))


def inverse_value(b):
    """( ( F : A -1-1-> B /\\ C e. A ) -> ( `' F ` ( F ` C ) ) = C )"""
    back = "( `' F ` ( F ` C ) ) = C"
    return ('gf1cnvfv1', f'|- ( ( F : A -1-1-> B /\\ C e. A ) -> {back} )',
            b.ap('sylan', {'ph': b.wff('F : A -1-1-> B'),
                           'ps': b.wff('F : A -1-1-onto-> ran F'),
                           'ch': b.wff('C e. A'), 'th': b.wff(back)},
                 b.ap('f1f1orn', {'F': b.rpn('F'), 'A': b.rpn('A'),
                                  'B': b.rpn('B')}),
                 b.ap('f1ocnvfv1', {'F': b.rpn('F'), 'A': b.rpn('A'),
                                    'B': b.rpn('ran F'), 'C': b.rpn('C')})))


def onto_bijection(b):
    """( ( A e. V /\\ F : A -1-1-> B /\\ A. y e. B E. x e. A y = ( F ` x ) )
    -> A ~~ B )
    """
    reach = 'A. y e. B E. x e. A y = ( F ` x )'
    held = f'( A e. V /\\ F : A -1-1-> B /\\ {reach} )'
    parts = {'ph': b.wff('A e. V'), 'ps': b.wff('F : A -1-1-> B'),
             'ch': b.wff(reach)}
    injective = b.ap('simp2', parts)
    reaches = b.ap('simp3', parts)
    function = b.ap('syl', {'ph': b.wff(held), 'ps': b.wff('F : A -1-1-> B'),
                            'ch': b.wff('F : A --> B')},
                    injective, b.ap('f1f', {'F': b.rpn('F'), 'A': b.rpn('A'),
                                            'B': b.rpn('B')}))
    onto = b.ap(
        'mpbir2and', {'ph': b.wff(held), 'ps': b.wff('F : A -onto-> B'),
                      'ch': b.wff('F : A --> B'), 'th': b.wff(reach)},
        function, reaches,
        b.ap('a1i', {'ph': b.wff(f'( F : A -onto-> B <-> '
                                 f'( F : A --> B /\\ {reach} ) )'),
                     'ps': b.wff(held)},
             b.ap('dffo3', {'F': b.rpn('F'), 'A': b.rpn('A'),
                            'B': b.rpn('B'), 'x': b.flabel['x'],
                            'y': b.flabel['y']})))
    both = b.ap(
        'mpbir2and', {'ph': b.wff(held), 'ps': b.wff('F : A -1-1-onto-> B'),
                      'ch': b.wff('F : A -1-1-> B'),
                      'th': b.wff('F : A -onto-> B')},
        injective, onto,
        b.ap('a1i', {'ph': b.wff('( F : A -1-1-onto-> B <-> ( F : A -1-1-> B '
                                 '/\\ F : A -onto-> B ) )'),
                     'ps': b.wff(held)},
             b.ap('df-f1o', {'F': b.rpn('F'), 'A': b.rpn('A'),
                             'B': b.rpn('B')})))
    return ('gf1foen', f'|- ( {held} -> A ~~ B )', b.ap(
        'syl2anc', {'ph': b.wff(held), 'ps': b.wff('A e. V'),
                    'ch': b.wff('F : A -1-1-onto-> B'), 'th': b.wff('A ~~ B')},
        b.ap('simp1', parts), both,
        b.ap('f1oeng', {'A': b.rpn('A'), 'C': b.rpn('V'), 'F': b.rpn('F'),
                        'B': b.rpn('B')})))
