$( tests/stdlib/geometry/ray-side-transfer, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.ray-side-transfer $p |- ( ( ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. CC ) /\ E e. CC ) /\ ( A = B \/ ( ( E - A ) / ( B - A ) ) e. RR ) ) /\ 0 < ( ( Im ` ( ( E - A ) / ( C - A ) ) ) x. ( Im ` ( ( B - A ) / ( C - A ) ) ) ) ) /\ -. ( A = D \/ ( ( B - A ) / ( D - A ) ) e. RR ) ) -> 0 < ( ( Im ` ( ( E - A ) / ( D - A ) ) ) x. ( Im ` ( ( B - A ) / ( D - A ) ) ) ) ) $=
    ( graysidetr ) BDACEF $.
$}
