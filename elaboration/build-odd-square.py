"""Assemble thm:odd-square as a Metamath proof.

Each readable step is one named block below, so the correspondence between the
proof text and the expansion stays visible.
"""

def seq(*p): return ' '.join(x for x in p if x)
def mul(a, b): return seq(a, b, 'cmul co')
def add(a, b): return seq(a, b, 'caddc co')
def exp(a, b): return seq(a, b, 'cexp co')
def inZZ(a): return seq(a, 'cz wcel')
def inCC(a): return seq(a, 'cc wcel')
def eq(a, b): return seq(a, b, 'wceq')
def wa(a, b): return seq(a, b, 'wa')
def dvds(a, b): return seq(a, b, 'cdvds wbr')

A, TWO, ONE, FOUR = 'cA', 'c2', 'c1', 'c4'
NV = 'vn cv'                      # the bound n, as a class
MV = 'vm cv'                      # the witness variable
NSQ = exp(NV, TWO)
W = add(mul(TWO, NSQ), mul(TWO, NV))          # 2n^2 + 2n
ASQ = exp(A, TWO)

EQN = eq(add(mul(TWO, NV), ONE), A)           # ( 2n + 1 ) = A
PHI = wa(inZZ(NV), EQN)                       # the scope an obtain opens

# --- step 1: the obtain becomes an existential -------------------------------
EXN = seq(EQN, 'vn cz wrex')
ODD = seq(dvds(TWO, A), 'wn')
step1 = seq(ODD, EXN, 'osq.2', inZZ(A), seq(ODD, EXN, 'wb'), 'osq.1',
            'vn', A, 'odd2np1 ax-mp mpbi')

# --- inside the scope --------------------------------------------------------
s1 = seq(inZZ(NV), EQN, 'simpl')                                  # ph -> n e. ZZ
s2 = seq(inZZ(NV), EQN, 'simpr')                                  # ph -> ( 2n+1 ) = A
s3 = seq(PHI, inZZ(NV), inCC(NV), s1, NV, 'zcn syl')              # ph -> n e. CC

# step 3 and step 4 of the readable proof, stubbed
SQ = exp(add(mul(TWO, NV), ONE), TWO)
MID = add(add(mul(FOUR, NSQ), mul(FOUR, NV)), ONE)
TARGET = add(mul(TWO, W), ONE)
s4 = seq(PHI, inCC(NV), eq(SQ, MID), s3, NV, 'oalg1 syl')
s5 = seq(PHI, inCC(NV), eq(MID, TARGET), s3, NV, 'oalg2 syl')

# step 5 of the readable proof: the calculation
s6 = seq(PHI, SQ, MID, TARGET, s4, s5, 'eqtrd')                   # ph -> SQ = TARGET
# step 2 of the readable proof: the substitute
s7 = seq(PHI, add(mul(TWO, NV), ONE), A, TWO, 'cexp', s2, 'oveq1d')
s8 = seq(PHI, SQ, TARGET, ASQ, s6, s7, 'eqtr3d')                  # ph -> TARGET = A^2

# the witness is an integer
two_zz = seq(inZZ(TWO), PHI, '2z a1i')
nsq_zz = seq(PHI, inZZ(NV), inZZ(NSQ), s1, NV, 'zsqcl syl')
a_zz = seq(PHI, TWO, NSQ, two_zz, nsq_zz, 'zmulcld')
b_zz = seq(PHI, TWO, NV, two_zz, s1, 'zmulcld')
s9 = seq(PHI, mul(TWO, NSQ), mul(TWO, NV), a_zz, b_zz, 'zaddcld')

# step 6 of the readable proof: the witness goes into an existential
EQM = eq(add(mul(TWO, MV), ONE), ASQ)
t1 = seq(MV, W, TWO, 'cmul oveq2')
t2 = seq(eq(MV, W), mul(TWO, MV), mul(TWO, W), ONE, 'caddc', t1, 'oveq1d')
t3 = seq(eq(MV, W), add(mul(TWO, MV), ONE), add(mul(TWO, W), ONE), ASQ, t2,
         'eqeq1d')
EXM = seq(EQM, 'vm cz wrex')
s10 = seq(PHI, wa(inZZ(W), eq(TARGET, ASQ)), EXM,
          seq(PHI, inZZ(W), eq(TARGET, ASQ), s9, s8, 'jca'),
          EQM, eq(TARGET, ASQ), 'vm', W, 'cz', t3, 'rspcev', 'syl')

# the conclusion, by the definition used the other way
asq_zz = seq(inZZ(A), inZZ(ASQ), 'osq.1', A, 'zsqcl ax-mp')
bic = seq(PHI, seq(dvds(TWO, ASQ), 'wn'), EXM,
          s10,
          seq(seq(seq(dvds(TWO, ASQ), 'wn'), EXM, 'wb'), PHI,
              seq(inZZ(ASQ), seq(seq(dvds(TWO, ASQ), 'wn'), EXM, 'wb'),
                  asq_zz, 'vm', ASQ, 'odd2np1 ax-mp'), 'a1i'),
          'mpbird')

body = seq(inZZ(NV), EQN, seq(dvds(TWO, ASQ), 'wn'), bic, 'ex')
final = seq(EXN, seq(dvds(TWO, ASQ), 'wn'),
            step1,
            seq(EQN, seq(dvds(TWO, ASQ), 'wn'), 'vn', 'cz', body, 'rexlimiv'),
            'ax-mp')

HEADER = """$( thm:odd-square, from proof/sqrt2-irrational.proof, as a Metamath proof.

   Verify with any Metamath verifier, with set.mm in the same directory:

       python3 mmverify.py odd-square.mm

   It was checked against set.mm of 2026-09-19 with mmverify.py, and against a
   copy of that file truncated after oddm1even, which is the last statement it
   uses.

   The two `algebra` steps are axioms here. Their expansion is the part the
   exercise does not settle; everything else is the real thing.
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
  osq.1 $e |- A e. ZZ $.
  osq.2 $e |- -. 2 || A $.
  oddsquare $p |- -. 2 || ( A ^ 2 ) $=
    {final} $.
$}}''')
