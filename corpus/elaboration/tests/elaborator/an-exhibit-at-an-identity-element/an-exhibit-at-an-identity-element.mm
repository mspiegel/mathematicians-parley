$( tests/elaborator/an-exhibit-at-an-identity-element/an-exhibit-at-an-identity-element, elaborated from tests/elaborator/an-exhibit-at-an-identity-element.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A r $.
  $d B r $.
  $d C r $.
  tests.elaborator.an-exhibit-at-an-identity-element.an-exhibit-at-an-identity-element $p |- ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ C = ( A + B ) ) -> E. r e. { 1 , 2 , 3 } C = ( A + ( r x. B ) ) ) $=
    ( cc wcel wa caddc co wceq c1 c2 c3 ctp cmul cv wrex cvv 1ex a1i tpid1g syl simpr eqcomd simpl mullid oveq2d eqeq1d mpbid jca id oveq1d eqeq2d rspcev ) AEFZBEFZGZCEFZGZCABHIZJZGZKKLMNZFZCAKBOIZHIZJZGCADPZBOIZHIZJZDVCQVBVDVGVBKRFZVDVLVBSTKRLMUAUBVBVFCVBUTCJVFCJVBCUTUSVAUCUDVBUTVFCVBVFUTVBVEBAHVBUPVEBJVBUSUPUSVAUEUSUQUPUQURUEUOUPUCUBUBBUFUBUGUDUHUIUDUJVKVGDKVCVHKJZVJVFCVMVIVEAHVMVHKBOVMUKULUGUMUNUB $.
$}
