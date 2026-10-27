$( tests/stdlib/geometry/three-points, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d j k m $.
  tests.stdlib.geometry.three-points $p |- E. m e. CC E. k e. CC E. j e. CC ( ( ( -. m = k /\ -. k = j ) /\ -. m = j ) /\ -. ( ( j - m ) / ( k - m ) ) e. RR ) $=
    ( cv wceq wn wa cmin co cdiv cr wcel cc wrex wtru gthreepts a1i mptru ) CDZBDZEZFZTADZEZFZGZSUCEZFZGZUCSHIZTSHIZJIZKLZFZGZAMNZBMNZCMNZUROCBAPQR $.
$}
