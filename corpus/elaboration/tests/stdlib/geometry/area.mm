$( tests/stdlib/geometry/area, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.geometry.area $p |- ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) -> ( ( ( 1 / 2 ) x. ( ( abs ` ( B - C ) ) x. ( abs ` ( A - C ) ) ) ) x. ( abs ` ( sin ` ( ( B - C ) ang ( A - C ) ) ) ) ) = ( ( ( 1 / 2 ) x. ( ( abs ` ( B - C ) ) x. ( abs ` ( A - C ) ) ) ) x. ( abs ` ( sin ` ( ( B - C ) ang ( A - C ) ) ) ) ) ) $=
    ( c1 c2 cdiv co cmin cabs cfv cmul cang csin wceq cc wcel wa eqid a1i ) DEFGZBCHGZIJZACHGZIJZKGZKGZUAUCLGZMJZIJZKGZUJNAOPBOPQCOPQUJRS $.
$}
