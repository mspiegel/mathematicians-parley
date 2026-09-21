"""Assemble thm:sqrt2-irrational as a Metamath proof.

Each readable step is one named block below, so the correspondence between the
proof text and the expansion stays visible.

The proof cites thm:even-square, which `parity.mm` proves, so this file builds
on that one rather than on set.mm directly. thm:lowest-terms and the three
`algebra` steps are axioms here; everything else is the real thing.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'parley'))

# `dvd` is division and `dvds` is the divisibility relation; the names are a
# letter apart here and this file uses both, so the quotient keeps its name.
from spell import cel, dvds, eq, exp, le, lt, mul, ne, rex, seq, w3a, wa, wb, wi, wn
from spell import div as dvd

TWO, ONE, ZERO, FOUR = 'c2', 'c1', 'cc0', 'c4'
PV, QV, RV, SV, DV, NV = ('vp cv', 'vq cv', 'vr cv', 'vs cv', 'vd cv',
                          'vn cv')
SQ2 = 'c2 csqrt cfv'
S = cel(SQ2, 'cq')
PQ, PSQ, QSQ, RSQ = dvd(PV, QV), exp(PV, TWO), exp(QV, TWO), exp(RV, TWO)

NOD = wn(rex(w3a(lt(ONE, DV), dvds(DV, PV), dvds(DV, QV)), 'vd', 'cz'))
BODY = w3a(lt(ZERO, QV), eq(SQ2, PQ), NOD)
EXPQ = rex(rex(BODY, 'vq', 'cz'), 'vp', 'cz')

CHPQ = wa(S, wa(cel(PV, 'cz'), cel(QV, 'cz')))
TH1 = wa(CHPQ, BODY)
TH2 = wa(wa(TH1, cel(RV, 'cz')), eq(mul(RV, TWO), PV))
TH3 = wa(wa(TH2, cel(SV, 'cz')), eq(mul(SV, TWO), QV))


def a1i(claim, th, pf):
    """th -> claim, from a closed proof of claim."""
    return seq(claim, th, pf, 'a1i')


def zcn(th, X, pf):
    return seq(th, cel(X, 'cz'), cel(X, 'cc'), pf, X, 'zcn', 'syl')


def zre(th, X, pf):
    return seq(th, cel(X, 'cz'), cel(X, 'cr'), pf, X, 'zre', 'syl')


def zsq(th, X, pf):
    return seq(th, cel(X, 'cz'), cel(exp(X, TWO), 'cz'), pf, X, 'zsqcl',
               'syl')


def adr(th, claim, added, pf):
    """( th /\\ added ) -> claim, from th -> claim."""
    return seq(th, claim, added, pf, 'adantr')


def lift(claim, pf, outer, adds):
    """Carry a fact proved at `outer` into the scope that `adds` opens."""
    for add in adds:
        pf = adr(outer, claim, add, pf)
        outer = wa(outer, add)
    return pf


# --- the three algebra steps ------------------------------------------------
# Step 3.8 is a normalisation with no cited equation, like odd-square's two.
# Steps 3.3 and 3.10 are the other half of the method: each takes a cited
# equation and multiplies through by a coefficient, which is ideal membership
# with one generator. set.mm's ring lemmas are over CC, so the expansion
# carries the atoms there and the readable text never says so.

AV, BV = 'cA', 'cB'
ASQV, BSQV = exp(AV, TWO), exp(BV, TWO)


def two_of(th, X, p_x):
    """th -> ( 2 x. ( 2 x. X ) ) = ( 4 x. X ), the one numeral fact needed."""
    assoc = seq(th, mul(mul(TWO, TWO), X), mul(TWO, mul(TWO, X)),
                seq(th, w3a(cel(TWO, 'cc'), cel(TWO, 'cc'), cel(X, 'cc')),
                    eq(mul(mul(TWO, TWO), X), mul(TWO, mul(TWO, X))),
                    seq(th, cel(TWO, 'cc'), cel(TWO, 'cc'), cel(X, 'cc'),
                        seq(th, '2cnd'), seq(th, '2cnd'), p_x, '3jca'),
                    TWO, TWO, X, 'mulass', 'syl'),
                'eqcomd')
    return seq(th, mul(TWO, mul(TWO, X)), mul(mul(TWO, TWO), X), mul(FOUR, X),
               assoc,
               seq(th, mul(TWO, TWO), FOUR, X, 'cmul',
                   a1i(eq(mul(TWO, TWO), FOUR), th, '2t2e4'), 'oveq1d'),
               'eqtrd')


# salg2: ( A x. 2 ) ^ 2 = 4 x. ( A ^ 2 ), a bare normalisation.
G2 = cel(AV, 'cc')
g2_a = seq(G2, 'id')
g2_asq = seq(G2, cel(AV, 'cc'), cel(ASQV, 'cc'), g2_a, AV, 'sqcl', 'syl')
salg2 = seq(G2, exp(mul(AV, TWO), TWO), mul(ASQV, exp(TWO, TWO)),
            mul(FOUR, ASQV),
            seq(G2, wa(cel(AV, 'cc'), cel(TWO, 'cc')),
                eq(exp(mul(AV, TWO), TWO), mul(ASQV, exp(TWO, TWO))),
                seq(G2, cel(AV, 'cc'), cel(TWO, 'cc'), g2_a, seq(G2, '2cnd'),
                    'jca'),
                AV, TWO, 'sqmul', 'syl'),
            seq(G2, mul(ASQV, exp(TWO, TWO)), mul(ASQV, FOUR), mul(FOUR, ASQV),
                seq(G2, exp(TWO, TWO), FOUR, ASQV, 'cmul',
                    a1i(eq(exp(TWO, TWO), FOUR), G2, 'sq2'), 'oveq2d'),
                seq(G2, ASQV, FOUR, g2_asq, a1i(cel(FOUR, 'cc'), G2, '4cn'),
                    'mulcomd'),
                'eqtrd'),
            'eqtrd')

# salg3: from 2A^2 = 4B^2 conclude A^2 = 2B^2, by cancelling the 2.
G3 = wa(cel(AV, 'cc'), cel(BV, 'cc'))
H3 = eq(mul(TWO, ASQV), mul(FOUR, BSQV))
T3 = wa(G3, H3)
g3_a = seq(G3, cel(AV, 'cc'), H3,
           seq(cel(AV, 'cc'), cel(BV, 'cc'), 'simpl'), 'adantr')
g3_b = seq(G3, cel(BV, 'cc'), H3,
           seq(cel(AV, 'cc'), cel(BV, 'cc'), 'simpr'), 'adantr')
g3_asq = seq(T3, cel(AV, 'cc'), cel(ASQV, 'cc'), g3_a, AV, 'sqcl', 'syl')
g3_bsq = seq(T3, cel(BV, 'cc'), cel(BSQV, 'cc'), g3_b, BV, 'sqcl', 'syl')
g3_2bsq = seq(T3, TWO, BSQV, seq(T3, '2cnd'), g3_bsq, 'mulcld')
salg3 = seq(T3, eq(mul(TWO, ASQV), mul(TWO, mul(TWO, BSQV))),
            eq(ASQV, mul(TWO, BSQV)),
            seq(T3, mul(TWO, ASQV), mul(FOUR, BSQV), mul(TWO, mul(TWO, BSQV)),
                seq(G3, H3, 'simpr'),
                seq(T3, mul(TWO, mul(TWO, BSQV)), mul(FOUR, BSQV),
                    two_of(T3, BSQV, g3_bsq), 'eqcomd'),
                'eqtrd'),
            seq(T3, ASQV, mul(TWO, BSQV), TWO, g3_asq, g3_2bsq,
                seq(T3, '2cnd'), a1i(ne(TWO, ZERO), T3, '2ne0'), 'mulcand'),
            'mpbid')
salg3 = seq(G3, H3, eq(ASQV, mul(TWO, BSQV)), salg3, 'ex')

# salg1: from ( A / B ) ^ 2 = 2 conclude A^2 = 2B^2, by clearing the divisor.
G1 = w3a(cel(AV, 'cr'), cel(BV, 'cr'), ne(BV, ZERO))
H1 = eq(exp(dvd(AV, BV), TWO), TWO)
T1 = wa(G1, H1)


def g1_up(claim, pf):
    return seq(G1, claim, H1, pf, 'adantr')


g1_ar = g1_up(cel(AV, 'cr'),
              seq(cel(AV, 'cr'), cel(BV, 'cr'), ne(BV, ZERO), 'simp1'))
g1_br = g1_up(cel(BV, 'cr'),
              seq(cel(AV, 'cr'), cel(BV, 'cr'), ne(BV, ZERO), 'simp2'))
g1_bne = g1_up(ne(BV, ZERO),
               seq(cel(AV, 'cr'), cel(BV, 'cr'), ne(BV, ZERO), 'simp3'))
g1_a = seq(T1, AV, g1_ar, 'recnd')
g1_b = seq(T1, BV, g1_br, 'recnd')
g1_asq = seq(T1, cel(AV, 'cc'), cel(ASQV, 'cc'), g1_a, AV, 'sqcl', 'syl')
g1_bsq = seq(T1, cel(BV, 'cc'), cel(BSQV, 'cc'), g1_b, BV, 'sqcl', 'syl')
g1_bsqne = seq(T1, ne(BSQV, ZERO), ne(BV, ZERO), g1_bne,
               seq(T1, cel(BV, 'cc'), wb(ne(BSQV, ZERO), ne(BV, ZERO)), g1_b,
                   BV, 'sqne0', 'syl'),
               'mpbird')
g1_div = seq(T1, exp(dvd(AV, BV), TWO), dvd(ASQV, BSQV), TWO,
             seq(T1, w3a(cel(AV, 'cc'), cel(BV, 'cc'), ne(BV, ZERO)),
                 eq(exp(dvd(AV, BV), TWO), dvd(ASQV, BSQV)),
                 seq(T1, cel(AV, 'cc'), cel(BV, 'cc'), ne(BV, ZERO), g1_a,
                     g1_b, g1_bne, '3jca'),
                 AV, BV, 'sqdiv', 'syl'),
             seq(G1, H1, 'simpr'), 'eqtr3d')
salg1 = seq(T1, ASQV, mul(BSQV, TWO), mul(TWO, BSQV),
            seq(T1, mul(BSQV, TWO), ASQV,
                seq(T1, eq(dvd(ASQV, BSQV), TWO), eq(mul(BSQV, TWO), ASQV),
                    g1_div,
                    seq(T1, ASQV, BSQV, TWO, g1_asq, g1_bsq, seq(T1, '2cnd'),
                        g1_bsqne, 'divmuld'),
                    'mpbid'),
                'eqcomd'),
            seq(T1, BSQV, TWO, g1_bsq, seq(T1, '2cnd'), 'mulcomd'), 'eqtrd')
salg1 = seq(G1, H1, eq(ASQV, mul(TWO, BSQV)), salg1, 'ex')

# --- steps 1 and 2, the two facts about the square root ---------------------
PRE = wa(cel(TWO, 'cr'), le(ZERO, TWO))
p_pre = seq(cel(TWO, 'cr'), le(ZERO, TWO), '2re 0le2 pm3.2i')
EQ1 = eq(exp(SQ2, TWO), TWO)
IN2 = cel(SQ2, 'cr')
step1 = seq(PRE, EQ1, p_pre, TWO, 'resqrtth', 'ax-mp')
step2 = seq(PRE, IN2, p_pre, TWO, 'resqrtcl', 'ax-mp')

# --- what the obtain of step 3.1 puts in scope ------------------------------
t_p = seq(S, cel(PV, 'cz'), cel(QV, 'cz'), BODY, 'simplrl')
t_q = seq(S, cel(PV, 'cz'), cel(QV, 'cz'), BODY, 'simplrr')
t_qpos = seq(CHPQ, lt(ZERO, QV), eq(SQ2, PQ), NOD, 'simpr1')
t_eq = seq(CHPQ, lt(ZERO, QV), eq(SQ2, PQ), NOD, 'simpr2')
t_nod = seq(CHPQ, lt(ZERO, QV), eq(SQ2, PQ), NOD, 'simpr3')

p_pzz, q_pzz = zsq(TH1, PV, t_p), zsq(TH1, QV, t_q)
p_pr, p_qr = zre(TH1, PV, t_p), zre(TH1, QV, t_q)

# --- step 3.2, substituting the obtained equation into line 1 ---------------
s32 = seq(TH1, exp(SQ2, TWO), exp(PQ, TWO), TWO,
          seq(TH1, SQ2, PQ, TWO, 'cexp', t_eq, 'oveq1d'),
          a1i(EQ1, TH1, step1), 'eqtr3d')

# --- step 3.3, the first algebra step ---------------------------------------
QNE = ne(QV, ZERO)
p_qne = seq(TH1, wa(cel(QV, 'cr'), lt(ZERO, QV)), QNE,
            seq(TH1, cel(QV, 'cr'), lt(ZERO, QV), p_qr, t_qpos, 'jca'),
            QV, 'gt0ne0', 'syl')
PRE33 = w3a(cel(PV, 'cr'), cel(QV, 'cr'), QNE)
EQ33 = eq(PSQ, mul(TWO, QSQ))
s33 = seq(TH1, eq(exp(PQ, TWO), TWO), EQ33, s32,
          seq(TH1, PRE33, wi(eq(exp(PQ, TWO), TWO), EQ33),
              seq(TH1, cel(PV, 'cr'), cel(QV, 'cr'), QNE, p_pr, p_qr, p_qne,
                  '3jca'),
              PV, QV, 'salg1', 'syl'), 'mpd')


def even_of(th, X, Y, p_eq, p_yzz, p_xzz):
    """th -> 2 || X, where p_eq proves th -> X = ( 2 x. Y ).

    This is `def:even` used to conclude, as step 6 of odd-square was. The
    kernel writes the witness equation as ( k x. 2 ) = X where the corpus
    writes X = 2k, so the two ends of it have to be turned round.
    """
    comm = seq(th, TWO, Y, a1i(cel(TWO, 'cc'), th, '2cn'), zcn(th, Y, p_yzz),
               'mulcomd')
    flip = seq(th, X, mul(Y, TWO),
               seq(th, X, mul(TWO, Y), mul(Y, TWO), p_eq, comm, 'eqtrd'),
               'eqcomd')
    PH, PS = eq(mul(NV, TWO), X), eq(mul(Y, TWO), X)
    hyp = seq(eq(NV, Y), mul(NV, TWO), mul(Y, TWO), X,
              seq(NV, Y, TWO, 'cmul', 'oveq1'), 'eqeq1d')
    EX = rex(PH, 'vn', 'cz')
    wit = seq(th, wa(cel(Y, 'cz'), PS), EX,
              seq(th, cel(Y, 'cz'), PS, p_yzz, flip, 'jca'),
              PH, PS, 'vn', Y, 'cz', hyp, 'rspcev', 'syl')
    bic = seq(th, wa(cel(TWO, 'cz'), cel(X, 'cz')), wb(dvds(TWO, X), EX),
              seq(th, cel(TWO, 'cz'), cel(X, 'cz'),
                  a1i(cel(TWO, 'cz'), th, '2z'), p_xzz, 'jca'),
              'vn', TWO, X, 'divides', 'syl')
    return seq(th, dvds(TWO, X), EX, wit, bic, 'mpbird')


def obtain_even(th, X, v, p_div, p_xzz):
    """th -> E. v e. ZZ ( v x. 2 ) = X, from th -> 2 || X.

    `divides` supplies the existential over its own bound variable n, and the
    readable proof names the obtained integer r and then s. Two obtains from
    one definition cannot share a name, so the rename is not optional.
    """
    VC = f'{v} cv'
    EXN, EXV = (rex(eq(mul(NV, TWO), X), 'vn', 'cz'),
                rex(eq(mul(VC, TWO), X), v, 'cz'))
    bic = seq(th, wa(cel(TWO, 'cz'), cel(X, 'cz')), wb(dvds(TWO, X), EXN),
              seq(th, cel(TWO, 'cz'), cel(X, 'cz'),
                  a1i(cel(TWO, 'cz'), th, '2z'), p_xzz, 'jca'),
              'vn', TWO, X, 'divides', 'syl')
    cbv = seq(eq(mul(NV, TWO), X), eq(mul(VC, TWO), X), 'vn', v, 'cz',
              seq(eq(NV, VC), mul(NV, TWO), mul(VC, TWO), X,
                  seq(NV, VC, TWO, 'cmul', 'oveq1'), 'eqeq1d'),
              'cbvrexv')
    return seq(th, EXN, EXV,
               seq(th, dvds(TWO, X), EXN, p_div, bic, 'mpbid'), cbv, 'sylib')


def close_scope(th, X, v, target, p_exv, body):
    """th -> target, discharging the existential the obtain opened."""
    VC = f'{v} cv'
    EQV = eq(mul(VC, TWO), X)
    return seq(th, rex(EQV, v, 'cz'), target, p_exv,
               seq(th, EQV, target, v, 'cz',
                   seq(wa(th, cel(VC, 'cz')), EQV, target, body, 'ex'),
                   'rexlimdva'), 'mpd')


# --- steps 3.4 and 3.5, p squared is even and so is p -----------------------
s34 = even_of(TH1, PSQ, QSQ, s33, q_pzz, p_pzz)
s35 = seq(TH1, wa(cel(PV, 'cz'), dvds(TWO, PSQ)), dvds(TWO, PV),
          seq(TH1, cel(PV, 'cz'), dvds(TWO, PSQ), t_p, s34, 'jca'),
          PV, 'evensq', 'syl')

# --- step 3.6 opens the second scope ----------------------------------------
UP2 = [cel(RV, 'cz'), eq(mul(RV, TWO), PV)]
t_r = seq(TH1, cel(RV, 'cz'), eq(mul(RV, TWO), PV), 'simplr')
t_eqr = seq(wa(TH1, cel(RV, 'cz')), eq(mul(RV, TWO), PV), 'simpr')

# --- steps 3.7 to 3.10, the same shape a second time ------------------------
R2SQ = exp(mul(RV, TWO), TWO)
s37 = seq(TH2, PV, mul(RV, TWO), TWO, 'cexp',
          seq(TH2, mul(RV, TWO), PV, t_eqr, 'eqcomd'), 'oveq1d')
s38 = seq(TH2, cel(RV, 'cc'), eq(R2SQ, mul(FOUR, RSQ)),
          zcn(TH2, RV, t_r), RV, 'salg2', 'syl')
s39 = seq(TH2, mul(TWO, QSQ), PSQ, mul(FOUR, RSQ),
          seq(TH2, PSQ, mul(TWO, QSQ), lift(EQ33, s33, TH1, UP2), 'eqcomd'),
          seq(TH2, PSQ, R2SQ, mul(FOUR, RSQ), s37, s38, 'eqtrd'), 'eqtrd')
EQ310 = eq(QSQ, mul(TWO, RSQ))
s310 = seq(TH2, eq(mul(TWO, QSQ), mul(FOUR, RSQ)), EQ310, s39,
           seq(TH2, wa(cel(QV, 'cc'), cel(RV, 'cc')),
               wi(eq(mul(TWO, QSQ), mul(FOUR, RSQ)), EQ310),
               seq(TH2, cel(QV, 'cc'), cel(RV, 'cc'),
                   zcn(TH2, QV, lift(cel(QV, 'cz'), t_q, TH1, UP2)),
                   zcn(TH2, RV, t_r), 'jca'),
               QV, RV, 'salg3', 'syl'), 'mpd')

# --- steps 3.11 and 3.12, and the third scope -------------------------------
s311 = even_of(TH2, QSQ, RSQ, s310, zsq(TH2, RV, t_r),
               lift(cel(QSQ, 'cz'), q_pzz, TH1, UP2))
s312 = seq(TH2, wa(cel(QV, 'cz'), dvds(TWO, QSQ)), dvds(TWO, QV),
           seq(TH2, cel(QV, 'cz'), dvds(TWO, QSQ),
               lift(cel(QV, 'cz'), t_q, TH1, UP2), s311, 'jca'),
           QV, 'evensq', 'syl')

UP3 = [cel(SV, 'cz'), eq(mul(SV, TWO), QV)]

# --- steps 3.14 to 3.16, the exhibit ----------------------------------------
# 3.14 and 3.15 change the word for what the kernel has already: `p is even`
# and `2 divides p` are one formula once def:even and def:divides are
# unfolded, so the two steps carry no kernel move of their own.
s314 = lift(dvds(TWO, PV), s35, TH1, UP2 + UP3)
s315 = lift(dvds(TWO, QV), s312, TH2, UP3)
PH16 = w3a(lt(ONE, DV), dvds(DV, PV), dvds(DV, QV))
PS16 = w3a(lt(ONE, TWO), dvds(TWO, PV), dvds(TWO, QV))
hyp16 = seq(eq(DV, TWO), lt(ONE, DV), lt(ONE, TWO), dvds(DV, PV),
            dvds(TWO, PV), dvds(DV, QV), dvds(TWO, QV),
            seq(DV, TWO, ONE, 'clt', 'breq2'),
            seq(DV, TWO, PV, 'cdvds', 'breq1'),
            seq(DV, TWO, QV, 'cdvds', 'breq1'), '3anbi123d')
s316 = seq(TH3, wa(cel(TWO, 'cz'), PS16), rex(PH16, 'vd', 'cz'),
           seq(TH3, cel(TWO, 'cz'), PS16, a1i(cel(TWO, 'cz'), TH3, '2z'),
               seq(TH3, lt(ONE, TWO), dvds(TWO, PV), dvds(TWO, QV),
                   a1i(lt(ONE, TWO), TH3, '1lt2'), s314, s315, '3jca'),
               'jca'),
           PH16, PS16, 'vd', TWO, 'cz', hyp16, 'rspcev', 'syl')

# --- step 3.17, the join, and the three scopes closing ----------------------
s317 = seq(TH3, rex(PH16, 'vd', 'cz'), wn(S), s316,
           lift(NOD, t_nod, TH1, UP2 + UP3), 'pm2.21dd')
close_s = close_scope(TH2, QV, 'vs', wn(S),
                      obtain_even(TH2, QV, 'vs', s312,
                                  lift(cel(QV, 'cz'), t_q, TH1, UP2)), s317)
close_r = close_scope(TH1, PV, 'vr', wn(S),
                      obtain_even(TH1, PV, 'vr', s35, t_p), close_s)

# --- step 3, the contradiction block ----------------------------------------
body_pq = seq(CHPQ, BODY, wn(S), close_r, 'ex')
disch = seq(S, BODY, wn(S), 'vp', 'vq', 'cz', 'cz', body_pq, 'rexlimdvva')
step3 = seq(wi(S, wn(S)), wn(S),
            seq(S, EXPQ, wn(S), seq(SQ2, 'vq', 'vp', 'vd', 'ltrm'),
                disch, 'mpd'),
            seq(S, 'pm2.01'), 'ax-mp')

# --- step 4, the definition of irrational -----------------------------------
DIFF = cel(SQ2, seq('cr', 'cq', 'cdif'))
step4 = seq(DIFF, wa(IN2, wn(S)),
            seq(IN2, wn(S), step2, step3, 'pm3.2i'),
            SQ2, 'cr', 'cq', 'eldif', 'mpbir')

HEADER = """$( thm:sqrt2-irrational, from proof/sqrt2-irrational.proof, as a
   Metamath proof.

   Verify with any Metamath verifier, with parity.mm and set.mm in the same
   directory:

       python3 mmverify.py sqrt2.mm

   It was checked against set.mm of 2026-09-19 with mmverify.py, and against a
   copy of that file truncated after oddm1even, which is the last statement it
   uses.

   thm:lowest-terms and the proof's three `algebra` steps are axioms here.
   Everything else uses set.mm's own theorems, or thm:even-square, which
   parity.mm proves.
$)

"""

print(HEADER + f'''$[ parity.mm $]

$( thm:lowest-terms, stated as its readable form states it. set.mm's nearest
   statement is qredeu, which gives a unique pair in ( ZZ X. NN ) whose gcd
   is 1; the shapes do not match, and closing the gap is a proof of its own. $)
${{
  $d p q r s d n $.  $d p q r s d n A $.
  ltrm $a |- ( A e. QQ -> E. p e. ZZ E. q e. ZZ ( 0 < q /\\ A = ( p / q ) /\\
               -. E. d e. ZZ ( 1 < d /\\ d || p /\\ d || q ) ) ) $.
$}}

$( The three `algebra` steps of the readable proof. salg2 is a normalisation
   with no cited equation; salg1 and salg3 each take one cited equation and
   multiply through by a coefficient. $)
salg1 $p |- ( ( A e. RR /\\ B e. RR /\\ B =/= 0 ) ->
              ( ( ( A / B ) ^ 2 ) = 2 -> ( A ^ 2 ) = ( 2 x. ( B ^ 2 ) ) ) ) $=
  {salg1} $.

salg2 $p |- ( A e. CC -> ( ( A x. 2 ) ^ 2 ) = ( 4 x. ( A ^ 2 ) ) ) $=
  {salg2} $.

salg3 $p |- ( ( A e. CC /\\ B e. CC ) ->
              ( ( 2 x. ( A ^ 2 ) ) = ( 4 x. ( B ^ 2 ) ) ->
                ( A ^ 2 ) = ( 2 x. ( B ^ 2 ) ) ) ) $=
  {salg3} $.

${{
  $d p q r s d n $.
  s2irr $p |- ( sqrt ` 2 ) e. ( RR \\ QQ ) $=
    {step4} $.
$}}''')
