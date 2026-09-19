$( thm:odd-square, from proof/sqrt2-irrational.proof, as a Metamath proof.

   Verify with any Metamath verifier, with set.mm in the same directory:

       python3 mmverify.py odd-square.mm

   It was checked against set.mm of 2026-09-19 with mmverify.py, and against a
   copy of that file truncated after oddm1even, which is the last statement it
   uses.

   The two `algebra` steps are axioms here. Their expansion is the part the
   exercise does not settle; everything else is the real thing.
$)

$[ set.mm $]

$( The two `algebra` steps of the readable proof, stubbed as axioms. Their
   expansion is the part this exercise does not settle. $)
oalg1 $a |- ( N e. CC -> ( ( ( 2 x. N ) + 1 ) ^ 2 ) =
             ( ( ( 4 x. ( N ^ 2 ) ) + ( 4 x. N ) ) + 1 ) ) $.
oalg2 $a |- ( N e. CC -> ( ( ( 4 x. ( N ^ 2 ) ) + ( 4 x. N ) ) + 1 ) =
             ( ( 2 x. ( ( 2 x. ( N ^ 2 ) ) + ( 2 x. N ) ) ) + 1 ) ) $.

${
  $d n m A $.
  osq.1 $e |- A e. ZZ $.
  osq.2 $e |- -. 2 || A $.
  oddsquare $p |- -. 2 || ( A ^ 2 ) $=
    c2 vn cv cmul co c1 caddc co cA wceq vn cz wrex c2 cA c2 cexp co cdvds wbr wn c2 cA cdvds wbr wn c2 vn cv cmul co c1 caddc co cA wceq vn cz wrex osq.2 cA cz wcel c2 cA cdvds wbr wn c2 vn cv cmul co c1 caddc co cA wceq vn cz wrex wb osq.1 vn cA odd2np1 ax-mp mpbi c2 vn cv cmul co c1 caddc co cA wceq c2 cA c2 cexp co cdvds wbr wn vn cz vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq c2 cA c2 cexp co cdvds wbr wn vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq wa c2 cA c2 cexp co cdvds wbr wn c2 vm cv cmul co c1 caddc co cA c2 cexp co wceq vm cz wrex vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq wa c2 vn cv c2 cexp co cmul co c2 vn cv cmul co caddc co cz wcel c2 c2 vn cv c2 cexp co cmul co c2 vn cv cmul co caddc co cmul co c1 caddc co cA c2 cexp co wceq wa c2 vm cv cmul co c1 caddc co cA c2 cexp co wceq vm cz wrex vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq wa c2 vn cv c2 cexp co cmul co c2 vn cv cmul co caddc co cz wcel c2 c2 vn cv c2 cexp co cmul co c2 vn cv cmul co caddc co cmul co c1 caddc co cA c2 cexp co wceq vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq wa c2 vn cv c2 cexp co cmul co c2 vn cv cmul co vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq wa c2 vn cv c2 cexp co c2 cz wcel vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq wa 2z a1i vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq wa vn cv cz wcel vn cv c2 cexp co cz wcel vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq simpl vn cv zsqcl syl zmulcld vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq wa c2 vn cv c2 cz wcel vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq wa 2z a1i vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq simpl zmulcld zaddcld vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq wa c2 vn cv cmul co c1 caddc co c2 cexp co c2 c2 vn cv c2 cexp co cmul co c2 vn cv cmul co caddc co cmul co c1 caddc co cA c2 cexp co vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq wa c2 vn cv cmul co c1 caddc co c2 cexp co c4 vn cv c2 cexp co cmul co c4 vn cv cmul co caddc co c1 caddc co c2 c2 vn cv c2 cexp co cmul co c2 vn cv cmul co caddc co cmul co c1 caddc co vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq wa vn cv cc wcel c2 vn cv cmul co c1 caddc co c2 cexp co c4 vn cv c2 cexp co cmul co c4 vn cv cmul co caddc co c1 caddc co wceq vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq wa vn cv cz wcel vn cv cc wcel vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq simpl vn cv zcn syl vn cv oalg1 syl vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq wa vn cv cc wcel c4 vn cv c2 cexp co cmul co c4 vn cv cmul co caddc co c1 caddc co c2 c2 vn cv c2 cexp co cmul co c2 vn cv cmul co caddc co cmul co c1 caddc co wceq vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq wa vn cv cz wcel vn cv cc wcel vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq simpl vn cv zcn syl vn cv oalg2 syl eqtrd vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq wa c2 vn cv cmul co c1 caddc co cA c2 cexp vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq simpr oveq1d eqtr3d jca c2 vm cv cmul co c1 caddc co cA c2 cexp co wceq c2 c2 vn cv c2 cexp co cmul co c2 vn cv cmul co caddc co cmul co c1 caddc co cA c2 cexp co wceq vm c2 vn cv c2 cexp co cmul co c2 vn cv cmul co caddc co cz vm cv c2 vn cv c2 cexp co cmul co c2 vn cv cmul co caddc co wceq c2 vm cv cmul co c1 caddc co c2 c2 vn cv c2 cexp co cmul co c2 vn cv cmul co caddc co cmul co c1 caddc co cA c2 cexp co vm cv c2 vn cv c2 cexp co cmul co c2 vn cv cmul co caddc co wceq c2 vm cv cmul co c2 c2 vn cv c2 cexp co cmul co c2 vn cv cmul co caddc co cmul co c1 caddc vm cv c2 vn cv c2 cexp co cmul co c2 vn cv cmul co caddc co c2 cmul oveq2 oveq1d eqeq1d rspcev syl c2 cA c2 cexp co cdvds wbr wn c2 vm cv cmul co c1 caddc co cA c2 cexp co wceq vm cz wrex wb vn cv cz wcel c2 vn cv cmul co c1 caddc co cA wceq wa cA c2 cexp co cz wcel c2 cA c2 cexp co cdvds wbr wn c2 vm cv cmul co c1 caddc co cA c2 cexp co wceq vm cz wrex wb cA cz wcel cA c2 cexp co cz wcel osq.1 cA zsqcl ax-mp vm cA c2 cexp co odd2np1 ax-mp a1i mpbird ex rexlimiv ax-mp $.
$}
