$( tests/stdlib/geometry/segment-point, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A m $.
  $d B m $.
  $d C m $.
  tests.stdlib.geometry.segment-point $p |- ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. RR ) /\ 0 < C ) /\ C < ( abs ` ( A - B ) ) ) -> E. m e. CC ( ( A =/= m /\ ( ( B - m ) / ( A - m ) ) e. RR /\ ( ( B - m ) / ( A - m ) ) < 0 ) /\ ( abs ` ( A - m ) ) = C ) ) $=
    ( gsegpt ) DABCE $.
$}
