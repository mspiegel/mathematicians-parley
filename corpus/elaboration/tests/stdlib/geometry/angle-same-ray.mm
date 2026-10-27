$( tests/stdlib/geometry/angle-same-ray, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.angle-same-ray $p |- ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. CC ) /\ ( B = C \/ ( ( D - B ) / ( C - B ) ) e. RR ) ) /\ 0 < ( ( Im ` ( ( D - B ) / ( A - B ) ) ) x. ( Im ` ( ( C - B ) / ( A - B ) ) ) ) ) -> ( abs ` ( ( A - B ) ang ( D - B ) ) ) = ( abs ` ( ( A - B ) ang ( C - B ) ) ) ) $=
    ( gangsameray ) BCADE $.
$}
