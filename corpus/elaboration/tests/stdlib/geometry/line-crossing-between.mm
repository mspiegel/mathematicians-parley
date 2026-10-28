$( tests/stdlib/geometry/line-crossing-between, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.line-crossing-between $p |- ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. CC ) /\ ( A = C \/ ( ( D - A ) / ( C - A ) ) e. RR ) ) /\ ( ( Im ` ( ( C - A ) / ( B - A ) ) ) x. ( Im ` ( ( D - A ) / ( B - A ) ) ) ) < 0 ) -> ( C =/= A /\ ( ( D - A ) / ( C - A ) ) e. RR /\ ( ( D - A ) / ( C - A ) ) < 0 ) ) $=
    ( glinecrossbet ) BACDE $.
$}
