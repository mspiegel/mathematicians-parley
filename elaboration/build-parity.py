"""Assemble thm:odd-square and thm:even-square as Metamath proofs.

Each readable step is one named block below, so the correspondence between the
proof text and the expansion stays visible.

A readable theorem's hypotheses become the antecedent of an implication rather
than Metamath essential hypotheses. Even-square cites odd-square inside a
contradiction block, where nothing is a proved statement and only an
implication can be applied.
"""

def seq(*p): return ' '.join(x for x in p if x)
def mul(a, b): return seq(a, b, 'cmul co')
def add(a, b): return seq(a, b, 'caddc co')
def exp(a, b): return seq(a, b, 'cexp co')
def inZZ(a): return seq(a, 'cz wcel')
def inCC(a): return seq(a, 'cc wcel')
def eq(a, b): return seq(a, b, 'wceq')
def wa(a, b): return seq(a, b, 'wa')
def wo(a, b): return seq(a, b, 'wo')
def wi(a, b): return seq(a, b, 'wi')
def wn(a): return seq(a, 'wn')
def dvds(a, b): return seq(a, b, 'cdvds wbr')

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

   The two `algebra` steps of odd-square are axioms here. Their expansion is
   the part the exercise does not settle; everything else is the real thing.
$)

"""

print(HEADER + f'''$[ set.mm $]

$( The two `algebra` steps of the readable proof, stubbed as axioms. Their
   expansion is the part this exercise does not settle. $)
oalg1 $a |- ( N e. CC -> ( ( ( 2 x. N ) + 1 ) ^ 2 ) =
             ( ( ( 4 x. ( N ^ 2 ) ) + ( 4 x. N ) ) + 1 ) ) $.
oalg2 $a |- ( N e. CC -> ( ( ( 4 x. ( N ^ 2 ) ) + ( 4 x. N ) ) + 1 ) =
             ( ( 2 x. ( ( 2 x. ( N ^ 2 ) ) + ( 2 x. N ) ) ) + 1 ) ) $.

${{
  $d n m A $.
  oddsq $p |- ( ( A e. ZZ /\\ -. 2 || A ) -> -. 2 || ( A ^ 2 ) ) $=
    {odd_proof} $.
$}}

${{
  evensq $p |- ( ( A e. ZZ /\\ 2 || ( A ^ 2 ) ) -> 2 || A ) $=
    {e_2} $.
$}}''')
