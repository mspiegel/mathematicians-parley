$( tests/notations/sums/a-product-scaled, elaborated from tests/notations/sums.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A x $.
  tests.notations.sums.a-product-scaled $p |- ( ( A e. ~P ZZ /\ A e. Fin ) -> prod_ x e. A ( x x. 3 ) = ( ( 3 ^ ( # ` A ) ) x. prod_ x e. A x ) ) $=
    ( cz cpw wcel cfn wa c3 cv cmul co cprod chash cfv cexp wceq 3z a1i wi simpr simpl id syl gfprodmulc mpd ) BCDZEZBFEZGZHCEZBAIZHJKZALZHBMNZOKZBUKALZJKZPZUJUIQRUIUHUJURSZUGUHTUIUGUHUSSUIUGUGUGUHUAUGUBUCHABUDUCUEUE $.
$}
