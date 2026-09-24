"""Assemble thm:proof/triangle-inequality/abs-bounds as a Metamath proof.

Each readable step is one named block below, so the correspondence between the
proof text and the expansion stays visible.

It is the first proof here with a `cases` block, which completes the four
block forms, and the first with any `inequalities` step expanded.

Nothing here is assumed.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'parley'))

from spell import cel, eq, le, lt, neg, seq, wa, wi, wo

X, ZERO = 'cX', 'cc0'
PH = cel(X, 'cr')
ABSX, NEGX = seq(X, 'cabs cfv'), neg(X)
CONCL = wa(le(X, ABSX), le(NEGX, ABSX))


def ai(claim, th, pf): return seq(claim, th, pf, 'a1i')


# --- step 1, every real is nonnegative or negative --------------------------
DISJ = wo(le(ZERO, X), lt(X, ZERO))
p1 = seq(PH, wa(cel(ZERO, 'cr'), cel(X, 'cr')), DISJ,
         seq(PH, cel(ZERO, 'cr'), cel(X, 'cr'), ai(cel(ZERO, 'cr'), PH, '0re'),
             seq(PH, 'id'), 'jca'),
         ZERO, X, 'lelttric', 'syl')

# --- the first case, x >= 0 -------------------------------------------------
# The case assumption and the theorem hypothesis together are exactly what
# absid wants, so the definition step is the bare lemma.
C1 = wa(PH, le(ZERO, X))
c1_x = seq(PH, le(ZERO, X), 'simpl')
c1_ge = seq(PH, le(ZERO, X), 'simpr')
p21 = seq(X, 'absid')
p21r = seq(C1, ABSX, X, p21, 'eqcomd')

p22 = seq(C1, X, X, ABSX, 'cle',
          seq(C1, cel(X, 'cr'), le(X, X), c1_x, X, 'leid', 'syl'), p21r,
          'breqtrd')
c1_neg = seq(C1, cel(X, 'cr'), cel(NEGX, 'cr'), c1_x, X, 'renegcl', 'syl')
p23 = seq(C1, NEGX, X, ABSX, 'cle',
          seq(C1, NEGX, ZERO, X, c1_neg, ai(cel(ZERO, 'cr'), C1, '0re'), c1_x,
              seq(C1, le(ZERO, X), le(NEGX, ZERO), c1_ge,
                  seq(C1, cel(X, 'cr'), seq(le(ZERO, X), le(NEGX, ZERO), 'wb'),
                      c1_x, X, 'le0neg2', 'syl'),
                  'mpbid'),
              c1_ge, 'letrd'),
          p21r, 'breqtrd')
case1 = seq(C1, le(X, ABSX), le(NEGX, ABSX), p22, p23, 'jca')

# --- the second case, x < 0 -------------------------------------------------
# Here the assumption is strict and absnid wants a non-strict one, so the
# definition step costs a step the text does not write.
C2 = wa(PH, lt(X, ZERO))
c2_x = seq(PH, lt(X, ZERO), 'simpl')
c2_lt = seq(PH, lt(X, ZERO), 'simpr')
c2_lex = seq(C2, lt(X, ZERO), le(X, ZERO), c2_lt,
             seq(C2, wa(cel(X, 'cr'), cel(ZERO, 'cr')),
                 wi(lt(X, ZERO), le(X, ZERO)),
                 seq(C2, cel(X, 'cr'), cel(ZERO, 'cr'), c2_x,
                     ai(cel(ZERO, 'cr'), C2, '0re'), 'jca'),
                 X, ZERO, 'ltle', 'syl'),
             'mpd')
p25 = seq(C2, wa(cel(X, 'cr'), le(X, ZERO)), eq(ABSX, NEGX),
          seq(C2, cel(X, 'cr'), le(X, ZERO), c2_x, c2_lex, 'jca'),
          X, 'absnid', 'syl')
p25r = seq(C2, ABSX, NEGX, p25, 'eqcomd')
c2_neg = seq(C2, cel(X, 'cr'), cel(NEGX, 'cr'), c2_x, X, 'renegcl', 'syl')

p26 = seq(C2, NEGX, NEGX, ABSX, 'cle',
          seq(C2, cel(NEGX, 'cr'), le(NEGX, NEGX), c2_neg, NEGX, 'leid',
              'syl'),
          p25r, 'breqtrd')
p27 = seq(C2, X, NEGX, ABSX, 'cle',
          seq(C2, X, ZERO, NEGX, c2_x, ai(cel(ZERO, 'cr'), C2, '0re'), c2_neg,
              c2_lex,
              seq(C2, le(X, ZERO), le(ZERO, NEGX), c2_lex,
                  seq(C2, cel(X, 'cr'), seq(le(X, ZERO), le(ZERO, NEGX), 'wb'),
                      c2_x, X, 'le0neg1', 'syl'),
                  'mpbid'),
              'letrd'),
          p25r, 'breqtrd')
# 2.8 joins 2.6 and 2.7 in that order, but the theorem states the conjuncts
# the other way round, so the pair is built in the conclusion's order.
case2 = seq(C2, le(X, ABSX), le(NEGX, ABSX), p27, p26, 'jca')

# --- step 2, the cases block closing ----------------------------------------
proof = seq(PH, le(ZERO, X), CONCL, lt(X, ZERO), case1, case2, p1, 'mpjaodan')

HEADER = """$( thm:proof/triangle-inequality/abs-bounds, from
   proof/triangle-inequality.proof, as a Metamath proof.

   Verify with any Metamath verifier, with set.mm in the same directory:

       python3 mmverify.py abs-bounds.mm

   It was checked against set.mm of 2026-09-19 with mmverify.py and with the
   metamath program, and against a copy of that file truncated after
   oddm1even.

   Nothing here is assumed.
$)

"""

print(HEADER + f'''$[ set.mm $]

absbnd $p |- ( X e. RR ->
    ( X <_ ( abs ` X ) /\\ -u X <_ ( abs ` X ) ) ) $=
  {proof} $.''')
