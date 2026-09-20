"""Assemble thm:sqrt2-irrational as a Metamath proof.

Each readable step is one named block below, so the correspondence between the
proof text and the expansion stays visible.

The proof cites thm:even-square, which `parity.mm` proves, so this file builds
on that one rather than on set.mm directly. thm:lowest-terms and the three
`algebra` steps are axioms here; everything else is the real thing.
"""

def seq(*p): return ' '.join(x for x in p if x)
def co(a, b, f): return seq(a, b, f, 'co')
def mul(a, b): return co(a, b, 'cmul')
def dvd(a, b): return co(a, b, 'cdiv')
def exp(a, b): return co(a, b, 'cexp')
def cel(a, b): return seq(a, b, 'wcel')
def br(a, b, r): return seq(a, b, r, 'wbr')
def dvds(a, b): return br(a, b, 'cdvds')
def lt(a, b): return br(a, b, 'clt')
def le(a, b): return br(a, b, 'cle')
def ne(a, b): return seq(a, b, 'wne')
def eq(a, b): return seq(a, b, 'wceq')
def wa(a, b): return seq(a, b, 'wa')
def w3a(a, b, c): return seq(a, b, c, 'w3a')
def wn(a): return seq(a, 'wn')
def wi(a, b): return seq(a, b, 'wi')
def wb(a, b): return seq(a, b, 'wb')
def rex(body, v, A): return seq(body, v, A, 'wrex')

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

$( The three `algebra` steps of the readable proof, stubbed as axioms. Their
   expansion is the part this exercise does not settle. $)
salg1 $a |- ( ( A e. RR /\\ B e. RR /\\ B =/= 0 ) ->
              ( ( ( A / B ) ^ 2 ) = 2 -> ( A ^ 2 ) = ( 2 x. ( B ^ 2 ) ) ) ) $.
salg2 $a |- ( A e. CC -> ( ( A x. 2 ) ^ 2 ) = ( 4 x. ( A ^ 2 ) ) ) $.
salg3 $a |- ( ( A e. CC /\\ B e. CC ) ->
              ( ( 2 x. ( A ^ 2 ) ) = ( 4 x. ( B ^ 2 ) ) ->
                ( A ^ 2 ) = ( 2 x. ( B ^ 2 ) ) ) ) $.

${{
  $d p q r s d n $.
  s2irr $p |- ( sqrt ` 2 ) e. ( RR \\ QQ ) $=
    {step4} $.
$}}''')
