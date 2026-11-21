$( tests/stdlib/geometry/same-side-off-line, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.same-side-off-line $p |- ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. CC ) /\ 0 < ( ( Im ` ( ( C - A ) / ( B - A ) ) ) x. ( Im ` ( ( D - A ) / ( B - A ) ) ) ) ) -> ( ( -. A = B /\ -. ( A = B \/ ( ( C - A ) / ( B - A ) ) e. RR ) ) /\ -. ( A = B \/ ( ( D - A ) / ( B - A ) ) e. RR ) ) ) $=
    ( cc wcel wa cc0 cmin co cdiv cim cfv cmul clt wbr wceq wn cr wo wne gsameoffab wb df-ne a1i mpbid gsameoffp jca gsameoffq ) AEFZBEFZGZCEFZGZDEFZGZHCAIJZBAIJZKJZLMZDAIJZURKJZLMZNJZOPZGZABQZRZVGUSSFZTZRZGVGVBSFTRVFVHVKVFABUAZVHABCDUBVLVHUCVFABUDUEUFABCDUGUHABCDUIUH $.
$}
