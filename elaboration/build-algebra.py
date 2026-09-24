"""Assemble step 3 of thm:proof/bezout/least-combination-divides as a Metamath proof.

It is the one `algebra` step in the corpus whose coefficients are not
constants. The step combines three cited equations with coefficients -1, 1 and
-q, where every other step in the corpus either cites nothing or uses constant
coefficients, so it is the case that decides whether `algebra` has one lemma
order or needs a search.

It does not: the order the five smaller steps follow carries this one too. What
is new is the price of the hypotheses. Ten atoms all have to be in CC, and the
proof carries that conjunction into every line, which is most of its size.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'parley'))

from spell import add, cel, eq, mul, seq, sub, w3a, wa, wb

A, B, C, D, U, V, X, Y, Q, R = ('cA', 'cB', 'cC', 'cD', 'cU', 'cV', 'cX',
                                'cY', 'cQ', 'cR')
ATOMS = [A, B, C, D, U, V, X, Y, Q, R]


def conj(parts):
    out = parts[0]
    for p in parts[1:]:
        out = wa(out, p)
    return out


MEM = [cel(a, 'cc') for a in ATOMS]
GH = conj(MEM)

E1 = eq(C, add(mul(Q, D), R))            # from line 2
E2 = eq(C, add(mul(A, U), mul(B, V)))    # H9
E3 = eq(D, add(mul(A, X), mul(B, Y)))    # H10
HYP = w3a(E1, E2, E3)
TH = wa(GH, HYP)


def pick(i):
    """GH -> MEM[i], by walking out of the left-nested conjunction."""
    if i == 0:
        pf, k = seq(MEM[0], MEM[1], 'simpl'), 2
    else:
        pf, k = seq(conj(MEM[:i]), MEM[i], 'simpr'), i + 1
    while k < len(MEM):
        pf = seq(conj(MEM[:k + 1]), conj(MEM[:k]), MEM[i],
                 seq(conj(MEM[:k]), MEM[k], 'simpl'), pf, 'syl')
        k += 1
    return pf


CC = {a: seq(GH, cel(a, 'cc'), HYP, pick(i), 'adantr')
      for i, a in enumerate(ATOMS)}


def prod(a, b): return seq(TH, a, b, CC[a], CC[b], 'mulcld')


h1 = seq(GH, E1, E2, E3, 'simpr1')
h2 = seq(GH, E1, E2, E3, 'simpr2')
h3 = seq(GH, E1, E2, E3, 'simpr3')

AU, BV, AX, BY = mul(A, U), mul(B, V), mul(A, X), mul(B, Y)
QX, QY, QD = mul(Q, X), mul(Q, Y), mul(Q, D)
p_au, p_bv, p_ax, p_by = prod(A, U), prod(B, V), prod(A, X), prod(B, Y)
p_qx, p_qy, p_qd = prod(Q, X), prod(Q, Y), prod(Q, D)
p_aqx = seq(TH, A, QX, CC[A], p_qx, 'mulcld')
p_bqy = seq(TH, B, QY, CC[B], p_qy, 'mulcld')

# R = C - ( Q x. D ), from C = ( Q x. D ) + R.
back = seq(TH, sub(C, QD), R,
           seq(TH, eq(sub(C, QD), R), eq(add(QD, R), C),
               seq(TH, C, add(QD, R), h1, 'eqcomd'),
               seq(TH, w3a(cel(C, 'cc'), cel(QD, 'cc'), cel(R, 'cc')),
                   wb(eq(sub(C, QD), R), eq(add(QD, R), C)),
                   seq(TH, cel(C, 'cc'), cel(QD, 'cc'), cel(R, 'cc'),
                       CC[C], p_qd, CC[R], '3jca'),
                   C, QD, R, 'subadd', 'syl'),
               'mpbird'),
           'eqcomd')

# and the two cited equations go in.
sub_in = seq(TH, C, add(AU, BV), QD, mul(Q, add(AX, BY)), 'cmin', h2,
             seq(TH, D, add(AX, BY), Q, 'cmul', h3, 'oveq2d'), 'oveq12d')

# Q x. ( AX + BY ) = A x. ( Q x. X ) + B x. ( Q x. Y )
distr = seq(TH, w3a(cel(Q, 'cc'), cel(AX, 'cc'), cel(BY, 'cc')),
            eq(mul(Q, add(AX, BY)), add(mul(Q, AX), mul(Q, BY))),
            seq(TH, cel(Q, 'cc'), cel(AX, 'cc'), cel(BY, 'cc'),
                CC[Q], p_ax, p_by, '3jca'),
            Q, AX, BY, 'adddi', 'syl')


def swap(f, g, h, p_f, p_g, p_h):
    """TH -> ( f x. ( g x. h ) ) = ( g x. ( f x. h ) )."""
    return seq(TH, w3a(cel(f, 'cc'), cel(g, 'cc'), cel(h, 'cc')),
               eq(mul(f, mul(g, h)), mul(g, mul(f, h))),
               seq(TH, cel(f, 'cc'), cel(g, 'cc'), cel(h, 'cc'), p_f, p_g,
                   p_h, '3jca'),
               f, g, h, 'mul12', 'syl')


regroup = seq(TH, mul(Q, AX), mul(A, QX), mul(Q, BY), mul(B, QY), 'caddc',
              swap(Q, A, X, CC[Q], CC[A], CC[X]),
              swap(Q, B, Y, CC[Q], CC[B], CC[Y]), 'oveq12d')
qterm = seq(TH, mul(Q, add(AX, BY)), add(mul(Q, AX), mul(Q, BY)),
            add(mul(A, QX), mul(B, QY)), distr, regroup, 'eqtrd')

# ( AU + BV ) - ( A(QX) + B(QY) ) = ( AU - A(QX) ) + ( BV - B(QY) )
split = seq(TH, wa(wa(cel(AU, 'cc'), cel(BV, 'cc')),
                   wa(cel(mul(A, QX), 'cc'), cel(mul(B, QY), 'cc'))),
            eq(sub(add(AU, BV), add(mul(A, QX), mul(B, QY))),
               add(sub(AU, mul(A, QX)), sub(BV, mul(B, QY)))),
            seq(TH, wa(cel(AU, 'cc'), cel(BV, 'cc')),
                wa(cel(mul(A, QX), 'cc'), cel(mul(B, QY), 'cc')),
                seq(TH, cel(AU, 'cc'), cel(BV, 'cc'), p_au, p_bv, 'jca'),
                seq(TH, cel(mul(A, QX), 'cc'), cel(mul(B, QY), 'cc'), p_aqx,
                    p_bqy, 'jca'), 'jca'),
            AU, BV, mul(A, QX), mul(B, QY), 'addsub4', 'syl')


def factor(f, g, h, p_g, p_h):
    """TH -> ( ( f x. g ) - ( f x. h ) ) = ( f x. ( g - h ) )."""
    return seq(TH, mul(f, sub(g, h)), sub(mul(f, g), mul(f, h)),
               seq(TH, w3a(cel(f, 'cc'), cel(g, 'cc'), cel(h, 'cc')),
                   eq(mul(f, sub(g, h)), sub(mul(f, g), mul(f, h))),
                   seq(TH, cel(f, 'cc'), cel(g, 'cc'), cel(h, 'cc'), CC[f],
                       p_g, p_h, '3jca'),
                   f, g, h, 'subdi', 'syl'),
               'eqcomd')


TARGET = add(mul(A, sub(U, QX)), mul(B, sub(V, QY)))
refactor = seq(TH, sub(AU, mul(A, QX)), mul(A, sub(U, QX)),
               sub(BV, mul(B, QY)), mul(B, sub(V, QY)), 'caddc',
               factor(A, U, QX, CC[U], p_qx), factor(B, V, QY, CC[V], p_qy),
               'oveq12d')

RHS0 = sub(add(AU, BV), mul(Q, add(AX, BY)))
RHS1 = sub(add(AU, BV), add(mul(A, QX), mul(B, QY)))
RHS2 = add(sub(AU, mul(A, QX)), sub(BV, mul(B, QY)))
norm = seq(TH, RHS0, RHS2, TARGET,
           seq(TH, RHS0, RHS1, RHS2,
               seq(TH, mul(Q, add(AX, BY)), add(mul(A, QX), mul(B, QY)),
                   add(AU, BV), 'cmin', qterm, 'oveq2d'),
               split, 'eqtrd'),
           refactor, 'eqtrd')

proof = seq(TH, R, sub(C, QD), TARGET, back,
            seq(TH, sub(C, QD), RHS0, TARGET, sub_in, norm, 'eqtrd'), 'eqtrd')
proof = seq(GH, HYP, eq(R, TARGET), proof, 'ex')

def cj(parts):
    out = parts[0]
    for p in parts[1:]:
        out = f'( {out} /\\ {p} )'
    return out


GH_TXT = cj([f'{n} e. CC' for n in 'ABCDUVXYQR'])
HYP_TXT = ('( C = ( ( Q x. D ) + R ) /\\ C = ( ( A x. U ) + ( B x. V ) ) '
           '/\\ D = ( ( A x. X ) + ( B x. Y ) ) )')
OUT_TXT = 'R = ( ( A x. ( U - ( Q x. X ) ) ) + ( B x. ( V - ( Q x. Y ) ) ) )'

HEADER = """$( Step 3 of thm:proof/bezout/least-combination-divides, from
   proof/bezout.proof, as a Metamath proof.

   Verify with any Metamath verifier, with set.mm in the same directory:

       python3 mmverify.py algebra.mm

   It was checked against set.mm of 2026-09-19 with mmverify.py and with the
   metamath program, and against a copy of that file truncated after
   oddm1even.

   Nothing here is assumed.
$)

"""

print(HEADER + f'''$[ set.mm $]

$( r = a ( u - q x0 ) + b ( v - q y0 ), from c = q d + r, c = a u + b v and
   d = a x0 + b y0. The three cited equations enter with coefficients -1, 1
   and -q. $)
balg1 $p |- ( {GH_TXT} -> ( {HYP_TXT} -> {OUT_TXT} ) ) $=
  {proof} $.''')
