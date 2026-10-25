$( tests/elaborator/a-point-said-back-over-the-plane/a-point-said-back-over-the-plane, elaborated from tests/elaborator/a-point-said-back-over-the-plane.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A m $.
  $d B m $.
  tests.elaborator.a-point-said-back-over-the-plane.a-point-said-back-over-the-plane $p |- ( ( ( A e. CC /\ B e. CC ) /\ ( abs ` ( A - B ) ) = 1 ) -> E. m e. CC ( abs ` ( m - B ) ) = 1 ) $=
    ( cc wcel wa cmin co cabs cfv c1 wceq cv wrex simpl id syl simpr jca oveq1d fveq2d eqeq1d rspcev ) ADEZBDEZFZABGHZIJZKLZFZUDUIFCMZBGHZIJZKLZCDNUJUDUIUJUFUDUFUIOUFUDUDUDUEOUDPQQUFUIRSUNUICADUKALZUMUHKUOULUGIUOUKABGUOPTUAUBUCQ $.
$}
