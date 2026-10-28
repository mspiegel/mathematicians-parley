$( tests/stdlib/geometry/on-off-apart, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.on-off-apart $p |- ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. CC ) /\ ( A = B \/ ( ( C - A ) / ( B - A ) ) e. RR ) ) /\ -. ( A = B \/ ( ( D - A ) / ( B - A ) ) e. RR ) ) -> -. C = D ) $=
    ( cc wcel wa wceq cmin co cdiv cr wo wn wne gonoffapart wb df-ne a1i mpbid ) AEFZBEFZGZCEFZGZDEFZGZABHZCAIJZBAIJZKJZLFZMZGZUHDAIJZUJKJZLFZMZNZGZCDOZCDHZNZABCDPVAVCQUTCDRST $.
$}
