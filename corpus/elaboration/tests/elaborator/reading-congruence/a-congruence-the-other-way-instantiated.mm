$( tests/elaborator/reading-congruence/a-congruence-the-other-way-instantiated, elaborated from tests/elaborator/reading-congruence.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A x $.
  $d B x $.
  tests.elaborator.reading-congruence.a-congruence-the-other-way-instantiated $p |- ( ( ( A e. ZZ /\ B e. NN ) /\ A. x e. ZZ B || ( ( x ^ 2 ) - x ) ) -> B || ( A - ( A ^ 2 ) ) ) $=
    ( cz wcel cn wa cv c2 cexp co cmin cdvds wbr wral simpr wi simpl id syl wceq oveq1d oveq12d breq2d rspcv mpd nnz cn0 2nn0 a1i zexpcld gcongcomd mpbid ) BDEZCFEZGZCAHZIJKZUQLKZMNZADOZGZCBIJKZBLKZMNZCBVCLKMNVBVAVEUPVAPVBUNVAVEQVBUPUNUPVARZUPUNUNUNUORZUNSZTZTZUTVEABDUQBUAZUSVDCMVKURVCUQBLVKUQBIJVKSZUBVLUCUDUETUFVBVCBCVBUOCDEVBUPUOVFUNUOPTCUGTVBBIVJIUHEVBUIUJUKVJULUM $.
$}
