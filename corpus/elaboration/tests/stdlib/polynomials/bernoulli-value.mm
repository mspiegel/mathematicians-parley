$( tests/stdlib/polynomials/bernoulli-value, elaborated from tests/stdlib/polynomials.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A k $.
  $d B k $.
  tests.stdlib.polynomials.bernoulli-value $p |- ( ( A e. NN0 /\ B e. CC ) -> ( A BernPoly B ) = ( ( B ^ A ) - sum_ k e. ( 0 ... ( A - 1 ) ) ( ( A _C k ) x. ( ( k BernPoly B ) / ( ( A - k ) + 1 ) ) ) ) ) $=
    ( bpolyval ) CABD $.
$}
