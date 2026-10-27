$( tests/stdlib/geometry/off-line-swap, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.off-line-swap $p |- ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ -. ( A = B \/ ( ( C - A ) / ( B - A ) ) e. RR ) ) -> -. ( A = C \/ ( ( B - A ) / ( C - A ) ) e. RR ) ) $=
    ( goffswap ) BCAD $.
$}
