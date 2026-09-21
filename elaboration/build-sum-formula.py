"""Assemble thm:sum-formula as a Metamath proof.

Each readable step is one named block below, so the correspondence between the
proof text and the expansion stays visible.

It is the first proof here with an `induction` and the first with a `fix`, and
the first whose definition is recursive. set.mm proves the same statement as
`arisum`; citing it would test nothing, so the proof follows the readable one
and uses `nnind` with the base and step blocks the text writes.

Nothing here is assumed.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'parley'))

from spell import add, cel, eq, fz, mul, ne, seq, summ, w3a, wa
from spell import div as dv

ONE, TWO, ZERO = 'c1', 'c2', 'cc0'
KV = 'vk cv'

S1 = summ(fz(ONE, ONE), KV, 'vk')
RHS1 = dv(mul(ONE, add(ONE, ONE)), TWO)

# 1.1  S(1) = 1, the base sentence of def:S.
p11 = seq(cel(ONE, 'cz'), cel(ONE, 'cc'), eq(S1, ONE), '1z', 'ax-1cn',
          seq(KV, ONE, 'vk', ONE, seq(eq(KV, ONE), 'id'), 'fsum1'), 'mp2an')

# 1.2  1 = 1( 1 + 1 ) / 2, the arithmetic step.
e_m1 = seq(eq(add(ONE, ONE), TWO),
           eq(mul(ONE, add(ONE, ONE)), mul(ONE, TWO)), '1p1e2',
           seq(add(ONE, ONE), TWO, ONE, 'cmul', 'oveq2'), 'ax-mp')
e_m2 = seq(cel(TWO, 'cc'), eq(mul(ONE, TWO), TWO), '2cn',
           seq(TWO, 'mullid'), 'ax-mp')
e_num = seq(mul(ONE, add(ONE, ONE)), mul(ONE, TWO), TWO, e_m1, e_m2, 'eqtri')
e_div = seq(eq(mul(ONE, add(ONE, ONE)), TWO), eq(RHS1, dv(TWO, TWO)), e_num,
            seq(mul(ONE, add(ONE, ONE)), TWO, TWO, 'cdiv', 'oveq1'), 'ax-mp')
e_dd = seq(cel(TWO, 'cc'), ne(TWO, ZERO), eq(dv(TWO, TWO), ONE), '2cn',
           '2ne0', seq(TWO, 'divid'), 'mp2an')
p12 = seq(RHS1, ONE, seq(RHS1, dv(TWO, TWO), ONE, e_div, e_dd, 'eqtri'),
          'eqcomi')

# 1.3  the calculation joining them.
base = seq(S1, ONE, RHS1, p11, p12, 'eqtri')


# --- the step block, 1.4 ----------------------------------------------------
def ai(claim, th, pf): return seq(claim, th, pf, 'a1i')


YV = 'vy cv'
Y1 = add(YV, ONE)
SY = summ(fz(ONE, YV), KV, 'vk')
SY1 = summ(fz(ONE, Y1), KV, 'vk')
RY = dv(mul(YV, Y1), TWO)
RY1 = dv(mul(Y1, add(Y1, ONE)), TWO)
IH = eq(SY, RY)
TH = wa(cel(YV, 'cn'), IH)

p_y = seq(cel(YV, 'cn'), IH, 'simpl')
p_ih = seq(cel(YV, 'cn'), IH, 'simpr')
p_ycn = seq(TH, cel(YV, 'cn'), cel(YV, 'cc'), p_y, YV, 'nncn', 'syl')
p_1cn = ai(cel(ONE, 'cc'), TH, 'ax-1cn')
p_2cn = seq(TH, '2cnd')
p_2ne = ai(ne(TWO, ZERO), TH, '2ne0')
p_y1cn = seq(TH, YV, ONE, p_ycn, p_1cn, 'addcld')
p_y2cn = seq(TH, YV, TWO, p_ycn, p_2cn, 'addcld')
p_yy1 = seq(TH, YV, Y1, p_ycn, p_y1cn, 'mulcld')
p_2y1 = seq(TH, TWO, Y1, p_2cn, p_y1cn, 'mulcld')

# 1.4.1  the step sentence of def:S, which is where the recursion unfolds.
#
# fsump1 requires that its bound variable not occur in the antecedent, and the
# induction hypothesis is an equation between sums, so it mentions that
# variable. The recursion is therefore unfolded before the hypothesis enters,
# under `y e. NN` alone, and carried in afterwards.
NNY = cel(YV, 'cn')
IN_FZ = wa(NNY, cel(KV, fz(ONE, Y1)))
p_uz = seq(NNY, YV, 'cn', seq(ONE, 'cuz cfv'), seq(NNY, 'id'), 'nnuz',
           'eleqtrdi')
p_kcc = seq(IN_FZ, cel(KV, 'cz'), cel(KV, 'cc'),
            seq(IN_FZ, cel(KV, fz(ONE, Y1)), cel(KV, 'cz'),
                seq(NNY, cel(KV, fz(ONE, Y1)), 'simpr'),
                seq(KV, ONE, Y1, 'elfzelz'), 'syl'),
            KV, 'zcn', 'syl')
p141 = seq(NNY, eq(SY1, add(SY, Y1)), IH,
           seq(NNY, KV, Y1, 'vk', ONE, YV, p_uz, p_kcc,
               seq(eq(KV, Y1), 'id'), 'fsump1'),
           'adantr')

# 1.4.2  the induction hypothesis goes in.
p142 = seq(TH, SY, RY, Y1, 'caddc', p_ih, 'oveq1d')

# 1.4.3  the algebra step, proved in the direction the identity runs and then
# turned round, as the readable line states it the other way.
e_y2 = seq(TH, add(Y1, ONE), add(YV, add(ONE, ONE)), add(YV, TWO),
           seq(TH, YV, ONE, ONE, p_ycn, p_1cn, p_1cn, 'addassd'),
           seq(TH, add(ONE, ONE), TWO, YV, 'caddc',
               ai(eq(add(ONE, ONE), TWO), TH, '1p1e2'), 'oveq2d'),
           'eqtrd')
e_dir = seq(TH, w3a(cel(YV, 'cc'), cel(TWO, 'cc'), cel(Y1, 'cc')),
            eq(mul(add(YV, TWO), Y1), add(mul(YV, Y1), mul(TWO, Y1))),
            seq(TH, cel(YV, 'cc'), cel(TWO, 'cc'), cel(Y1, 'cc'), p_ycn,
                p_2cn, p_y1cn, '3jca'),
            YV, TWO, Y1, 'adddir', 'syl')
e_top = seq(TH, mul(Y1, add(Y1, ONE)), mul(Y1, add(YV, TWO)),
            add(mul(YV, Y1), mul(TWO, Y1)),
            seq(TH, add(Y1, ONE), add(YV, TWO), Y1, 'cmul', e_y2, 'oveq2d'),
            seq(TH, mul(Y1, add(YV, TWO)), mul(add(YV, TWO), Y1),
                add(mul(YV, Y1), mul(TWO, Y1)),
                seq(TH, Y1, add(YV, TWO), p_y1cn, p_y2cn, 'mulcomd'),
                e_dir, 'eqtrd'),
            'eqtrd')
e_dd = seq(TH, w3a(cel(mul(YV, Y1), 'cc'), cel(mul(TWO, Y1), 'cc'),
                   wa(cel(TWO, 'cc'), ne(TWO, ZERO))),
           eq(dv(add(mul(YV, Y1), mul(TWO, Y1)), TWO),
              add(dv(mul(YV, Y1), TWO), dv(mul(TWO, Y1), TWO))),
           seq(TH, cel(mul(YV, Y1), 'cc'), cel(mul(TWO, Y1), 'cc'),
               wa(cel(TWO, 'cc'), ne(TWO, ZERO)), p_yy1, p_2y1,
               seq(TH, cel(TWO, 'cc'), ne(TWO, ZERO), p_2cn, p_2ne, 'jca'),
               '3jca'),
           mul(YV, Y1), mul(TWO, Y1), TWO, 'divdir', 'syl')
e_can = seq(TH, w3a(cel(Y1, 'cc'), cel(TWO, 'cc'), ne(TWO, ZERO)),
            eq(dv(mul(TWO, Y1), TWO), Y1),
            seq(TH, cel(Y1, 'cc'), cel(TWO, 'cc'), ne(TWO, ZERO), p_y1cn,
                p_2cn, p_2ne, '3jca'),
            Y1, TWO, 'divcan3', 'syl')
p143 = seq(TH, RY1, add(RY, Y1),
           seq(TH, RY1, add(RY, dv(mul(TWO, Y1), TWO)), add(RY, Y1),
               seq(TH, RY1, dv(add(mul(YV, Y1), mul(TWO, Y1)), TWO),
                   add(RY, dv(mul(TWO, Y1), TWO)),
                   seq(TH, mul(Y1, add(Y1, ONE)),
                       add(mul(YV, Y1), mul(TWO, Y1)), TWO, 'cdiv', e_top,
                       'oveq1d'),
                   e_dd, 'eqtrd'),
               seq(TH, dv(mul(TWO, Y1), TWO), Y1, RY, 'caddc', e_can,
                   'oveq2d'),
               'eqtrd'),
           'eqcomd')

# 1.4.4  the calculation.
p144 = seq(TH, SY1, add(SY, Y1), RY1, p141,
           seq(TH, add(SY, Y1), add(RY, Y1), RY1, p142, p143, 'eqtrd'),
           'eqtrd')
step = seq(cel(YV, 'cn'), IH, eq(SY1, RY1), p144, 'ex')


# --- step 1, the induction itself -------------------------------------------
# nnind wants the claim at four instances of its variable, and the readable
# line never writes any of them: the text says only "induction on n starting
# at 1". Each is built by congruence out of x = T.
XV, AV = 'vx cv', 'cA'


def claim(T):
    return eq(summ(fz(ONE, T), KV, 'vk'), dv(mul(T, add(T, ONE)), TWO))


def instance(T):
    """( x = T -> ( claim(x) <-> claim(T) ) )."""
    at = eq(XV, T)
    idp = seq(at, 'id')
    e_sum = seq(at, eq(fz(ONE, XV), fz(ONE, T)),
                eq(summ(fz(ONE, XV), KV, 'vk'), summ(fz(ONE, T), KV, 'vk')),
                seq(at, XV, T, ONE, 'cfz', idp, 'oveq2d'),
                seq(fz(ONE, XV), fz(ONE, T), KV, 'vk', 'sumeq1'), 'syl')
    e_rhs = seq(at, mul(XV, add(XV, ONE)), mul(T, add(T, ONE)), TWO, 'cdiv',
                seq(at, XV, T, add(XV, ONE), add(T, ONE), 'cmul', idp,
                    seq(at, XV, T, ONE, 'caddc', idp, 'oveq1d'), 'oveq12d'),
                'oveq1d')
    return seq(at, summ(fz(ONE, XV), KV, 'vk'), summ(fz(ONE, T), KV, 'vk'),
               dv(mul(XV, add(XV, ONE)), TWO), dv(mul(T, add(T, ONE)), TWO),
               e_sum, e_rhs, 'eqeq12d')


proof = seq(claim(XV), claim(ONE), claim(YV), claim(Y1), claim(AV),
            'vx', 'vy', AV,
            instance(ONE), instance(YV), instance(Y1), instance(AV),
            base, step, 'nnind')

HEADER = """$( thm:sum-formula, from proof/sum-formula.proof, as a Metamath
   proof.

   Verify with any Metamath verifier, with set.mm in the same directory:

       python3 mmverify.py sum-formula.mm

   It was checked against set.mm of 2026-09-19 with mmverify.py and with the
   metamath program, and against a copy of that file truncated after
   oddm1even.

   set.mm proves this statement as arisum. It is not cited; the proof follows
   the readable one. Nothing here is assumed.
$)

"""

print(HEADER + f'''$[ set.mm $]

${{
  $d k x y A $.
  sumform $p |- ( A e. NN ->
      sum_ k e. ( 1 ... A ) k = ( ( A x. ( A + 1 ) ) / 2 ) ) $=
    {proof} $.
$}}''')
