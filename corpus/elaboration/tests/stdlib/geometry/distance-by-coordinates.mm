$( tests/stdlib/geometry/distance-by-coordinates, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.distance-by-coordinates $p |- ( ( ( ( A e. RR /\ B e. RR ) /\ C e. RR ) /\ D e. RR ) -> ( abs ` ( ( A + ( _i x. B ) ) - ( C + ( _i x. D ) ) ) ) = ( sqrt ` ( ( ( A - C ) ^ 2 ) + ( ( B - D ) ^ 2 ) ) ) ) $=
    ( cr wcel wa ci cmul co caddc cmin cabs cfv c2 cexp csqrt wceq simpl id syl simpr jca gdistco ) AEFZBEFZGZCEFZGZDEFZGZUGUHUJGZGAHBIJKJCHDIJKJLJMNACLJOPJBDLJOPJKJQNRUKUGULUKUEUFUKUIUEUIUJSZUIUGUEUGUHSZUGUEUEUEUFSUETUAUAUAUKUIUFUMUIUGUFUNUEUFUBUAUAUCUKUHUJUKUIUHUMUGUHUBUAUIUJUBUCUCABCDUDUA $.
$}
