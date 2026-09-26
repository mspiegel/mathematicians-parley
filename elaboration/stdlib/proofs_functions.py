"""Functions and their images, for `proved.mm`.

What Schröder–Bernstein asks of functions that set.mm says in two steps and
the page in one. Each lemma is a chain of two or three set.mm lemmas:

- what is in an image: `fvelimab` says it of a function on A, which `ffn`
  reads off f : A → B, with its equation turned by `eqcom` to the page's
  u = f(s), for `def:stdlib/functions/image`;
- a value lies in the image of a set holding its point: `fnfvima`, with
  `ffn` the same way, for `thm:stdlib/functions/value-in-image`;
- a one-to-one function's inverse undoes it: `f1f1orn` makes it a bijection
  onto its range, where `f1ocnvfv1` applies, for
  `thm:stdlib/functions/inverse-value`;
- a function that is one-to-one and reaches every point is a bijection:
  `dffo3` reads the reaching as onto, `df-f1o` puts the two together, and
  `f1oeng` gives the bijection, for `thm:stdlib/functions/onto-bijection`;
- a map sends its domain into a set exactly when each value lies there:
  `fmpt` says it of a name for the map, and `eqid` names the map itself,
  for `thm:stdlib/functions/function-into`.
"""

HEAD = """$( Functions: images, inverses, and a bijection from one-to-one and
   onto. $)
$d x y A $.
$d x y B $.
$d x y F $.
$d x D $.
$d x S $.

"""


def proofs(b):
    """(label, statement, proof) for each lemma."""
    return [image_member(b), inverse_value(b), onto_bijection(b),
            map_into(b), value_in_image(b)]


def image_member(b):
    """( ( F : A --> B /\\ S C_ A ) ->
    ( D e. ( F " S ) <-> E. x e. S D = ( F ` x ) ) )
    """
    held = '( F : A --> B /\\ S C_ A )'
    member = 'D e. ( F " S )'
    theirs = 'E. x e. S ( F ` x ) = D'
    ours = 'E. x e. S D = ( F ` x )'
    set_mm = b.ap('sylan', {'ph': b.wff('F : A --> B'), 'ps': b.wff('F Fn A'),
                            'ch': b.wff('S C_ A'),
                            'th': b.wff(f'( {member} <-> {theirs} )')},
                  b.ap('ffn', {'F': b.rpn('F'), 'A': b.rpn('A'),
                               'B': b.rpn('B')}),
                  b.ap('fvelimab', {'F': b.rpn('F'), 'A': b.rpn('A'),
                                    'B': b.rpn('S'), 'C': b.rpn('D'),
                                    'x': b.flabel['x']}))
    turned = b.ap('rexbii', {'ph': b.wff('( F ` x ) = D'),
                             'ps': b.wff('D = ( F ` x )'),
                             'x': b.flabel['x'], 'A': b.rpn('S')},
                  b.ap('eqcom', {'A': b.rpn('( F ` x )'), 'B': b.rpn('D')}))
    return ('gfvelima', f'|- ( {held} -> ( {member} <-> {ours} ) )', b.ap(
        'bitrdi', {'ph': b.wff(held), 'ps': b.wff(member),
                   'ch': b.wff(theirs), 'th': b.wff(ours)}, set_mm, turned))


def value_in_image(b):
    """( ( F : A --> B /\\ S C_ A /\\ D e. S ) -> ( F ` D ) e. ( F " S ) )"""
    says = '( F ` D ) e. ( F " S )'
    return ('gfnfvima',
            f'|- ( ( F : A --> B /\\ S C_ A /\\ D e. S ) -> {says} )',
            b.ap('syl3an1', {'ph': b.wff('F : A --> B'),
                             'ps': b.wff('F Fn A'), 'ch': b.wff('S C_ A'),
                             'th': b.wff('D e. S'), 'ta': b.wff(says)},
                 b.ap('ffn', {'F': b.rpn('F'), 'A': b.rpn('A'),
                              'B': b.rpn('B')}),
                 b.ap('fnfvima', {'F': b.rpn('F'), 'A': b.rpn('A'),
                                  'S': b.rpn('S'), 'X': b.rpn('D')})))


def map_into(b):
    """( A. x e. A C e. B <-> ( x e. A |-> C ) : A --> B )"""
    mapped = '( x e. A |-> C )'
    return ('gfmpt', f'|- ( A. x e. A C e. B <-> {mapped} : A --> B )',
            b.ap('fmpt', {'x': b.flabel['x'], 'A': b.rpn('A'),
                          'C': b.rpn('C'), 'B': b.rpn('B'),
                          'F': b.rpn(mapped)},
                 b.ap('eqid', {'A': b.rpn(mapped)})))


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
