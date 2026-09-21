"""Assemble thm:odd-square and thm:even-square as Metamath proofs.

Each readable step is one named block below, so the correspondence between the
proof text and the expansion stays visible.

A readable theorem's hypotheses become the antecedent of an implication rather
than Metamath essential hypotheses. Even-square cites odd-square inside a
contradiction block, where nothing is a proved statement and only an
implication can be applied.

The two `algebra` steps are proved rather than assumed. Both are
normalisations with no cited equation, and the second reuses the first's
pieces, which is the fixed lemma order METHODS.md asks `algebra` for.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'parley'))

from spell import add, cel, dvds, eq, exp, mul, seq, w3a, wa, wi, wn, wo


def inZZ(a): return cel(a, 'cz')
def inCC(a): return cel(a, 'cc')

A, TWO, ONE, FOUR = 'cA', 'c2', 'c1', 'c4'
NV = 'vn cv'                      # the bound n, as a class
MV = 'vm cv'                      # the witness variable
NSQ, ASQ = exp(NV, TWO), exp(A, TWO)
W = add(mul(TWO, NSQ), mul(TWO, NV))          # 2n^2 + 2n

EQN = eq(add(mul(TWO, NV), ONE), A)           # ( 2n + 1 ) = A
EXN = seq(EQN, 'vn cz wrex')
ODD_A, ODD_ASQ = wn(dvds(TWO, A)), wn(dvds(TWO, ASQ))

CH = wa(inZZ(A), ODD_A)           # odd-square's two hypotheses, conjoined
CHN = wa(CH, inZZ(NV))
TH = wa(CHN, EQN)                 # and the scope the obtain opens

# --- the two algebra steps --------------------------------------------------
# Both are normalisations with no cited equation, which is what twelve of the
# corpus's seventeen algebra steps are. set.mm's ring lemmas are over CC, so
# the expansion carries the atom there and the readable text never says so.

NC = 'cN'
ALG = inCC(NC)                    # the one hypothesis an identity needs
NCSQ, TNC = exp(NC, TWO), mul(TWO, NC)


def ai(claim, pf): return seq(claim, ALG, pf, 'a1i')


a_n = seq(ALG, 'id')
a_2 = ai(inCC(TWO), '2cn')
a_1 = ai(inCC(ONE), 'ax-1cn')
a_tn = seq(ALG, TWO, NC, a_2, a_n, 'mulcld')
a_nsq = seq(ALG, inCC(NC), inCC(NCSQ), a_n, NC, 'sqcl', 'syl')


def double(X, p_x):
    """ALG -> ( 2 x. ( 2 x. X ) ) = ( 4 x. X ).

    Twice-two is the only numeral fact these identities need, and it is
    reached the same way each time: associate, then replace the product of
    numerals. Three of the five uses below are this one call."""
    assoc = seq(ALG, mul(mul(TWO, TWO), X), mul(TWO, mul(TWO, X)),
                seq(ALG, w3a(inCC(TWO), inCC(TWO), inCC(X)),
                    eq(mul(mul(TWO, TWO), X), mul(TWO, mul(TWO, X))),
                    seq(ALG, inCC(TWO), inCC(TWO), inCC(X), a_2, a_2, p_x,
                        '3jca'),
                    TWO, TWO, X, 'mulass', 'syl'),
                'eqcomd')
    numeral = seq(ALG, mul(TWO, TWO), FOUR, X, 'cmul',
                  ai(eq(mul(TWO, TWO), FOUR), '2t2e4'), 'oveq1d')
    return seq(ALG, mul(TWO, mul(TWO, X)), mul(mul(TWO, TWO), X), mul(FOUR, X),
               assoc, numeral, 'eqtrd')


# oalg1, the square of a sum. binom2 gets close, and the three terms it leaves
# are what the rest of this settles.
B1, B2, B3 = exp(TNC, TWO), mul(TWO, mul(TNC, ONE)), exp(ONE, TWO)
BINOM = add(add(B1, B2), B3)
a_binom = seq(ALG, wa(inCC(TNC), inCC(ONE)),
              eq(exp(add(TNC, ONE), TWO), BINOM),
              seq(ALG, inCC(TNC), inCC(ONE), a_tn, a_1, 'jca'),
              TNC, ONE, 'binom2', 'syl')
a_first = seq(ALG, B1, mul(exp(TWO, TWO), NCSQ), mul(FOUR, NCSQ),
              seq(ALG, wa(inCC(TWO), inCC(NC)),
                  eq(B1, mul(exp(TWO, TWO), NCSQ)),
                  seq(ALG, inCC(TWO), inCC(NC), a_2, a_n, 'jca'),
                  TWO, NC, 'sqmul', 'syl'),
              seq(ALG, exp(TWO, TWO), FOUR, NCSQ, 'cmul',
                  ai(eq(exp(TWO, TWO), FOUR), 'sq2'), 'oveq1d'),
              'eqtrd')
a_second = seq(ALG, B2, mul(TWO, TNC), mul(FOUR, NC),
               seq(ALG, mul(TNC, ONE), TNC, TWO, 'cmul',
                   seq(ALG, inCC(TNC), eq(mul(TNC, ONE), TNC), a_tn, TNC,
                       'mulrid', 'syl'),
                   'oveq2d'),
               double(NC, a_n), 'eqtrd')
ALG1 = add(add(mul(FOUR, NCSQ), mul(FOUR, NC)), ONE)
oalg1 = seq(ALG, exp(add(TNC, ONE), TWO), BINOM, ALG1, a_binom,
            seq(ALG, add(B1, B2), add(mul(FOUR, NCSQ), mul(FOUR, NC)), B3, ONE,
                'caddc',
                seq(ALG, B1, mul(FOUR, NCSQ), B2, mul(FOUR, NC), 'caddc',
                    a_first, a_second, 'oveq12d'),
                ai(eq(B3, ONE), 'sq1'), 'oveq12d'),
            'eqtrd')

# oalg2, the regrouping. Distribute, then halve each term back.
WC = add(mul(TWO, NCSQ), mul(TWO, NC))
a_distr = seq(ALG, w3a(inCC(TWO), inCC(mul(TWO, NCSQ)), inCC(mul(TWO, NC))),
              eq(mul(TWO, WC),
                 add(mul(TWO, mul(TWO, NCSQ)), mul(TWO, mul(TWO, NC)))),
              seq(ALG, inCC(TWO), inCC(mul(TWO, NCSQ)), inCC(mul(TWO, NC)),
                  a_2, seq(ALG, TWO, NCSQ, a_2, a_nsq, 'mulcld'),
                  seq(ALG, TWO, NC, a_2, a_n, 'mulcld'), '3jca'),
              TWO, mul(TWO, NCSQ), mul(TWO, NC), 'adddi', 'syl')
a_inner = seq(ALG, mul(TWO, WC),
              add(mul(TWO, mul(TWO, NCSQ)), mul(TWO, mul(TWO, NC))),
              add(mul(FOUR, NCSQ), mul(FOUR, NC)), a_distr,
              seq(ALG, mul(TWO, mul(TWO, NCSQ)), mul(FOUR, NCSQ),
                  mul(TWO, mul(TWO, NC)), mul(FOUR, NC), 'caddc',
                  double(NCSQ, a_nsq), double(NC, a_n), 'oveq12d'),
              'eqtrd')
oalg2 = seq(ALG, add(mul(FOUR, NCSQ), mul(FOUR, NC)), mul(TWO, WC), ONE,
            'caddc',
            seq(ALG, mul(TWO, WC), add(mul(FOUR, NCSQ), mul(FOUR, NC)),
                a_inner, 'eqcomd'),
            'oveq1d')

# --- odd-square -------------------------------------------------------------

# Step 1, the obtain. The scope is opened by proving the rest of the proof out
# of TH, so what the later steps get is each conjunct of TH in turn.
p_chn = seq(CHN, EQN, 'simpl')
p_n = seq(TH, CH, inZZ(NV), p_chn, 'simprd')
p_ch = seq(TH, CH, inZZ(NV), p_chn, 'simpld')
p_azz = seq(TH, inZZ(A), ODD_A, p_ch, 'simpld')
p_eqn = seq(CHN, EQN, 'simpr')
p_ncc = seq(TH, inZZ(NV), inCC(NV), p_n, NV, 'zcn syl')

SQ = exp(add(mul(TWO, NV), ONE), TWO)
MID = add(add(mul(FOUR, NSQ), mul(FOUR, NV)), ONE)
TARGET = add(mul(TWO, W), ONE)

# Steps 3 and 4, the two algebra identities, each needing n in CC.
alg1 = seq(TH, inCC(NV), eq(SQ, MID), p_ncc, NV, 'oalg1 syl')
alg2 = seq(TH, inCC(NV), eq(MID, TARGET), p_ncc, NV, 'oalg2 syl')

# Step 5, the calculation: two equalities chained by transitivity.
calc = seq(TH, SQ, MID, TARGET, alg1, alg2, 'eqtrd')

# Step 2, the substitute: n sits in the base of the power, so oveq1.
subst = seq(TH, add(mul(TWO, NV), ONE), A, TWO, 'cexp', p_eqn, 'oveq1d')
p_tgt = seq(TH, SQ, TARGET, ASQ, calc, subst, 'eqtr3d')

# The first `requires` line of step 6: the witness is an integer.
two_zz = seq(inZZ(TWO), TH, '2z a1i')
nsq_zz = seq(TH, inZZ(NV), inZZ(NSQ), p_n, NV, 'zsqcl syl')
w_zz = seq(TH, mul(TWO, NSQ), mul(TWO, NV),
           seq(TH, TWO, NSQ, two_zz, nsq_zz, 'zmulcld'),
           seq(TH, TWO, NV, two_zz, p_n, 'zmulcld'), 'zaddcld')

# Step 6, the definition used to conclude an existence claim. The witness is
# W, read off the cited line, and rspcev wants the claim with m in its place.
EQM = eq(add(mul(TWO, MV), ONE), ASQ)
EXM = seq(EQM, 'vm cz wrex')
t1 = seq(MV, W, TWO, 'cmul oveq2')
t2 = seq(eq(MV, W), mul(TWO, MV), mul(TWO, W), ONE, 'caddc', t1, 'oveq1d')
t3 = seq(eq(MV, W), add(mul(TWO, MV), ONE), add(mul(TWO, W), ONE), ASQ, t2,
         'eqeq1d')
p_exm = seq(TH, wa(inZZ(W), eq(TARGET, ASQ)), EXM,
            seq(TH, inZZ(W), eq(TARGET, ASQ), w_zz, p_tgt, 'jca'),
            EQM, eq(TARGET, ASQ), 'vm', W, 'cz', t3, 'rspcev', 'syl')

# and the second `requires`: the thing claimed odd is an integer. Then the
# definition is read right to left, back to the divisibility form.
p_asqzz = seq(TH, inZZ(A), inZZ(ASQ), p_azz, A, 'zsqcl syl')
p_bic = seq(TH, inZZ(ASQ), seq(ODD_ASQ, EXM, 'wb'), p_asqzz, 'vm', ASQ,
            'odd2np1 syl')
inner = seq(TH, ODD_ASQ, EXM, p_exm, p_bic, 'mpbird')
body = seq(CHN, EQN, ODD_ASQ, inner, 'ex')

# and the scope closes: the existential discharges what was proved under it.
o_azz = seq(inZZ(A), ODD_A, 'simpl')
o_odd = seq(inZZ(A), ODD_A, 'simpr')
o_exn = seq(CH, ODD_A, EXN, o_odd,
            seq(CH, inZZ(A), seq(ODD_A, EXN, 'wb'), o_azz, 'vn', A,
                'odd2np1 syl'), 'mpbid')
odd_proof = seq(CH, EXN, ODD_ASQ, o_exn,
                seq(CH, EQN, ODD_ASQ, 'vn', 'cz', body, 'rexlimdva'), 'mpd')

# --- even-square ------------------------------------------------------------

CH2 = wa(inZZ(A), dvds(TWO, ASQ))             # its two hypotheses
CH2S = wa(CH2, ODD_A)                         # and the supposition of step 1
e_azz = seq(inZZ(A), dvds(TWO, ASQ), 'simpl')
e_ev = seq(inZZ(A), dvds(TWO, ASQ), 'simpr')

# Step 1.1: under the supposition, A squared is odd, by citing odd-square.
s_azz = seq(CH2S, CH2, inZZ(A), seq(CH2, ODD_A, 'simpl'), e_azz, 'syl')
s_odd = seq(CH2, ODD_A, 'simpr')
e_11 = seq(CH2S, CH, ODD_ASQ,
           seq(CH2S, inZZ(A), ODD_A, s_azz, s_odd, 'jca'), A, 'oddsq', 'syl')

# Step 1.2: but the hypothesis says it is even. The contradiction block closes
# on the two of them, and pm2.65d is what discharges the supposition: there is
# no separate expansion for the `join` that pairs them.
e_12 = seq(CH2, dvds(TWO, ASQ), e_ev, 'notnotd')
e_1 = seq(CH2, ODD_A, ODD_ASQ,
          seq(CH2, ODD_A, ODD_ASQ, e_11, 'ex'),
          seq(CH2, wn(ODD_ASQ), ODD_A, e_12, 'a1d'), 'pm2.65d')

# Steps 2 and 3: every integer is even or odd, and this one is not odd.
e_or = seq(wo(dvds(TWO, A), ODD_A), CH2, dvds(TWO, A), 'exmid a1i')
e_2 = seq(CH2, wo(dvds(TWO, A), ODD_A), dvds(TWO, A), e_or,
          seq(CH2, wn(ODD_A), wi(wo(dvds(TWO, A), ODD_A), dvds(TWO, A)),
              e_1, ODD_A, dvds(TWO, A), 'orel2 syl'), 'mpd')

HEADER = """$( thm:odd-square and thm:even-square, from
   proof/sqrt2-irrational.proof, as Metamath proofs.

   Verify with any Metamath verifier, with set.mm in the same directory:

       python3 mmverify.py parity.mm

   They were checked against set.mm of 2026-09-19 with mmverify.py, and
   against a copy of that file truncated after oddm1even, which is the last
   statement they use.

   Nothing here is assumed. Every statement is proved from set.mm's own
   theorems, including the two `algebra` steps.
$)

"""

print(HEADER + f'''$[ set.mm $]

$( The two `algebra` steps of the readable proof. Each is a normalisation
   with no cited equation, which is what twelve of the corpus's seventeen
   algebra steps are. $)
oalg1 $p |- ( N e. CC -> ( ( ( 2 x. N ) + 1 ) ^ 2 ) =
             ( ( ( 4 x. ( N ^ 2 ) ) + ( 4 x. N ) ) + 1 ) ) $=
  {oalg1} $.

oalg2 $p |- ( N e. CC -> ( ( ( 4 x. ( N ^ 2 ) ) + ( 4 x. N ) ) + 1 ) =
             ( ( 2 x. ( ( 2 x. ( N ^ 2 ) ) + ( 2 x. N ) ) ) + 1 ) ) $=
  {oalg2} $.

${{
  $d n m A $.
  oddsq $p |- ( ( A e. ZZ /\\ -. 2 || A ) -> -. 2 || ( A ^ 2 ) ) $=
    {odd_proof} $.
$}}

${{
  evensq $p |- ( ( A e. ZZ /\\ 2 || ( A ^ 2 ) ) -> 2 || A ) $=
    {e_2} $.
$}}''')
