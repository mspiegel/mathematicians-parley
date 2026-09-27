"""Numbers, for `proved.mm`.

What Euclid's algorithm asks of whole numbers that set.mm says only of a
wider system: a remainder on dividing an integer by a natural number is
less than the divisor. `modlt` says it of a real and a positive real, and
`zre` and `nnrp` reach those, for `thm:stdlib/divisibility/mod-less`.
"""

HEAD = """$( Numbers: a remainder is less than its divisor. $)

"""


def proofs(b):
    """(label, statement, proof[, hypotheses]) for each lemma."""
    return [mod_less(b)]


def mod_less(b):
    """( ( A e. ZZ /\\ B e. NN ) -> ( A mod B ) < B )"""
    return ('gzmodlt', '|- ( ( A e. ZZ /\\ B e. NN ) -> ( A mod B ) < B )',
            b.ap('syl2an', {'ph': b.wff('A e. ZZ'), 'ps': b.wff('A e. RR'),
                            'ta': b.wff('B e. NN'), 'ch': b.wff('B e. RR+'),
                            'th': b.wff('( A mod B ) < B')},
                 b.ap('zre', {'N': b.rpn('A')}),
                 b.ap('nnrp', {'A': b.rpn('B')}),
                 b.ap('modlt', {'A': b.rpn('A'), 'B': b.rpn('B')})))
