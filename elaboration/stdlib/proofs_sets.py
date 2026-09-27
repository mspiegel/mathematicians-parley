"""Sets, for `proved.mm`.

What the library says of sets that set.mm says in more than one step:

- a part of a set is in its power set: `elpw2g` read one way by `biimpar`,
  closed so that `settle` may use it as a side condition's lemma;
- what is in the parts of X with a property: `elrab` over the power set,
  and `elpw2g` reading a member of the power set as a part, for
  `def:stdlib/sets/part-builder`.
"""

HEAD = """$( Sets: the parts of a set with a property. $)
$d x ps $.
$d x A $.
$d x B $.

"""


def proofs(b):
    """(label, statement, proof[, hypotheses]) for each lemma."""
    return [part_in_power(b), part_member(b)]


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
