"""Numbers, for `proved.mm`.

What Euclid's algorithm asks of whole numbers that set.mm says only of a
wider system, or only as an equivalence:

- a number in ℕ₀ other than 0 is in ℕ: `elnnne0` read one way, for
  `thm:stdlib/numbers/nat0-nonzero`;
- a remainder on dividing an integer by a natural number is less than the
  divisor: `modlt`, which is said of a real and a positive real, reached
  through `zre` and `nnrp`, for `thm:stdlib/divisibility/mod-less`.
"""

HEAD = """$( Numbers: a nonzero member of NN0 is in NN, and a remainder is less
   than its divisor. $)

"""


def proofs(b):
    """(label, statement, proof[, hypotheses]) for each lemma."""
    return [nat0_nonzero(b), mod_less(b)]


def nat0_nonzero(b):
    """( ( N e. NN0 /\\ N =/= 0 ) -> N e. NN )"""
    return ('gnn0ne0nn', '|- ( ( N e. NN0 /\\ N =/= 0 ) -> N e. NN )', b.ap(
        'biimpri', {'ph': b.wff('N e. NN'),
                    'ps': b.wff('( N e. NN0 /\\ N =/= 0 )')},
        b.ap('elnnne0', {'N': b.rpn('N')})))


def mod_less(b):
    """( ( A e. ZZ /\\ B e. NN ) -> ( A mod B ) < B )"""
    return ('gzmodlt', '|- ( ( A e. ZZ /\\ B e. NN ) -> ( A mod B ) < B )',
            b.ap('syl2an', {'ph': b.wff('A e. ZZ'), 'ps': b.wff('A e. RR'),
                            'ta': b.wff('B e. NN'), 'ch': b.wff('B e. RR+'),
                            'th': b.wff('( A mod B ) < B')},
                 b.ap('zre', {'N': b.rpn('A')}),
                 b.ap('nnrp', {'A': b.rpn('B')}),
                 b.ap('modlt', {'A': b.rpn('A'), 'B': b.rpn('B')})))
