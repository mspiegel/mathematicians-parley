$( tests/elaborator/identity-left-out/an-exhibit-without-its-zero, elaborated from tests/elaborator/identity-left-out.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A q $.
  $d B q $.
  $d C q $.
  tests.elaborator.identity-left-out.an-exhibit-without-its-zero $p |- ( ( ( ( A e. ZZ /\ B e. NN ) /\ C e. ZZ ) /\ ( C x. B ) = A ) -> E. q e. ZZ ( ( q x. B ) + 0 ) = A ) $=
    ( cz wcel cn wa cmul co wceq cc0 caddc cv wrex simpl simpr syl eqcomd cc zcn nncn mulcld addrid eqeq2d mpbid jca id oveq1d eqeq1d rspcev ) AEFZBGFZHZCEFZHZCBIJZAKZHZUOUQLMJZAKZHDNZBIJZLMJZAKZDEOUSUOVAUSUPUOUPURPZUNUOQZRZUSAUTUSAUQKAUTKUSUQAUPURQSUSUQUTAUSUTUQUSUQTFUTUQKUSCBUSUOCTFVHCUARUSUMBTFUSUPUMVFUPUNUMUNUOPULUMQRRBUBRUCUQUDRSUEUFSUGVEVADCEVBCKZVDUTAVIVCUQLMVIVBCBIVIUHUIUIUJUKR $.
$}
