$( tests/stdlib/geometry/same-side-same, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.same-side-same $p |- ( ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. CC ) /\ E e. CC ) /\ 0 < ( ( Im ` ( ( C - A ) / ( B - A ) ) ) x. ( Im ` ( ( D - A ) / ( B - A ) ) ) ) ) /\ 0 < ( ( Im ` ( ( D - A ) / ( B - A ) ) ) x. ( Im ` ( ( E - A ) / ( B - A ) ) ) ) ) -> 0 < ( ( Im ` ( ( C - A ) / ( B - A ) ) ) x. ( Im ` ( ( E - A ) / ( B - A ) ) ) ) ) $=
    ( gsametr ) ABCDEF $.
$}
