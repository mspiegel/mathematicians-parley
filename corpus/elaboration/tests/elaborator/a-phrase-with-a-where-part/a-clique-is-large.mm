$( tests/elaborator/a-phrase-with-a-where-part/a-clique-is-large, elaborated from tests/elaborator/a-phrase-with-a-where-part.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A m $.
  $d B m $.
  $d C m $.
  $d D m $.
  tests.elaborator.a-phrase-with-a-where-part.a-clique-is-large $p |- ( ( ( ( ( ( A e. _V /\ B e. _V ) /\ A. m e. B m C_ A ) /\ C e. NN ) /\ D e. ~P A ) /\ ( ( C + 1 ) <_ ( # ` D ) /\ A. m e. ~P D ( ( # ` m ) = 2 -> m e. B ) ) ) -> ( C + 1 ) <_ ( # ` D ) ) $=
    ( cvv wcel wa cv wss wral cn cpw c1 caddc co chash cfv cle wbr c2 wceq wi simpr wb biid a1i mpbid simpld ) AFGZBFGZHZEIZAJZEBKZHZCLGZHZDAMZGZHZCNOPZDQRZSTZUMQRZUAUBZUMBGZUCZEDMZKZHZHZVDVJVLVKVKVAVKUDVKVKUEVLVKUFUGUHUI $.
$}
