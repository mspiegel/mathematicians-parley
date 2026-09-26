$( tests/stdlib/divisibility/gcd-commutes, elaborated from tests/stdlib/divisibility.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  gcdcommu $p |- ( ( A e. ZZ /\ B e. ZZ ) -> ( A gcd B ) = ( B gcd A ) ) $=
    ( gcdcom ) ABC $.
$}
