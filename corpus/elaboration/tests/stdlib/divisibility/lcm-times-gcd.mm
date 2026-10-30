$( tests/stdlib/divisibility/lcm-times-gcd, elaborated from tests/stdlib/divisibility.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.divisibility.lcm-times-gcd $p |- ( ( A e. ZZ /\ B e. ZZ ) -> ( ( A lcm B ) x. ( A gcd B ) ) = ( abs ` ( A x. B ) ) ) $=
    ( lcmgcd ) ABC $.
$}
