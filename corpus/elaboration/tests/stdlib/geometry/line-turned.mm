$( tests/stdlib/geometry/line-turned, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A u $.
  $d B u $.
  tests.stdlib.geometry.line-turned $p |- ( ( A e. CC /\ B e. CC ) -> { u e. CC | ( A = B \/ ( ( u - A ) / ( B - A ) ) e. RR ) } = { u e. CC | ( B = A \/ ( ( u - B ) / ( A - B ) ) e. RR ) } ) $=
    ( glineturn ) ABCD $.
$}
