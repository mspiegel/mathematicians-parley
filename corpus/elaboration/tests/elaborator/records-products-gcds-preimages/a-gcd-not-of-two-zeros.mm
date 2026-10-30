$( tests/elaborator/records-products-gcds-preimages/a-gcd-not-of-two-zeros, elaborated from tests/elaborator/records-products-gcds-preimages.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.records-products-gcds-preimages.a-gcd-not-of-two-zeros $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ -. ( A = 0 /\ B = 0 ) ) -> ( A gcd B ) e. NN ) $=
    ( gcdn0cl ) ABC $.
$}
