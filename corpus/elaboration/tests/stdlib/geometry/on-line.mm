$( tests/stdlib/geometry/on-line, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.geometry.on-line $p |- ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ ( B = C \/ ( ( A - B ) / ( C - B ) ) e. RR ) ) -> ( B = C \/ ( ( A - B ) / ( C - B ) ) e. RR ) ) $=
    ( cc wcel wa wceq cmin co cdiv cr wo simpr wb biid a1i mpbid ) ADEZBDEZFZCDEZFZBCGZABHIZCBHIZJIZKEZLZFZUHUHUBUHMUHUHNUIUHOPQ $.
$}
