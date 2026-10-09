$( tests/stdlib/divisibility/gcd-one, elaborated from tests/stdlib/divisibility.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.divisibility.gcd-one $p |- ( A e. ZZ -> ( A gcd 1 ) = 1 ) $=
    ( cz wcel c1 cgcd co wceq id gcd1 syl ) ABCZKADEFDGKHAIJ $.
$}
