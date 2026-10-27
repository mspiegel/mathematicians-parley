$( tests/stdlib/geometry/angle-addition-inside, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.angle-addition-inside $p |- ( ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. CC ) /\ ( ( ( -. A = B /\ -. B = C ) /\ -. A = C ) /\ -. ( ( C - A ) / ( B - A ) ) e. RR ) ) /\ 0 < ( ( Im ` ( ( D - A ) / ( B - A ) ) ) x. ( Im ` ( ( C - A ) / ( B - A ) ) ) ) ) /\ 0 < ( ( Im ` ( ( D - A ) / ( C - A ) ) ) x. ( Im ` ( ( B - A ) / ( C - A ) ) ) ) ) -> ( ( abs ` ( ( B - A ) ang ( D - A ) ) ) + ( abs ` ( ( D - A ) ang ( C - A ) ) ) ) = ( abs ` ( ( B - A ) ang ( C - A ) ) ) ) $=
    ( gangaddin ) ABCDE $.
$}
