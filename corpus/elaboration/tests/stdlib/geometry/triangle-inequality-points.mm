$( tests/stdlib/geometry/triangle-inequality-points, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.geometry.triangle-inequality-points $p |- ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) -> ( abs ` ( A - C ) ) <_ ( ( abs ` ( A - B ) ) + ( abs ` ( B - C ) ) ) ) $=
    ( cc wcel wa w3a cmin co cabs cfv caddc cle wbr simpl id syl simpr 3jca abs3dif ) ADEZBDEZFZCDEZFZUAUDUBGACHIJKABHIJKBCHIJKLIMNUEUAUDUBUEUCUAUCUDOZUCUAUAUAUBOUAPQQUCUDRUEUCUBUFUAUBRQSACBTQ $.
$}
