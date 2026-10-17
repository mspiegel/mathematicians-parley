$( tests/elaborator/records-products-gcds-preimages/a-gcd-scaled, elaborated from tests/elaborator/records-products-gcds-preimages.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.records-products-gcds-preimages.a-gcd-scaled $p |- ( ( A e. ZZ /\ B e. ZZ ) -> ( ( 3 x. A ) gcd ( 3 x. B ) ) = ( 3 x. ( A gcd B ) ) ) $=
    ( cz wcel wa c3 cn0 w3a cmul co cgcd wceq 3nn0 a1i simpl id syl simpr 3jca mulgcd ) ACDZBCDZEZFGDZUAUBHFAIJFBIJKJFABKJIJLUCUDUAUBUDUCMNUCUAUAUAUBOUAPQUAUBRSFABTQ $.
$}
