$( tests/stdlib/geometry/signed-angle-size, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.geometry.signed-angle-size $p |- ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) -> ( abs ` ( ( A - B ) ang ( C - B ) ) ) = ( abs ` ( ( A - B ) ang ( C - B ) ) ) ) $=
    ( cmin co cang cabs cfv wceq cc wcel wa eqid a1i ) ABDEZCBDEZFEZGHZRIAJKBJKLCJKLRMN $.
$}
