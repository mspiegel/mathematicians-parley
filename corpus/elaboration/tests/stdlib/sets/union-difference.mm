$( tests/stdlib/sets/union-difference, elaborated from tests/stdlib/sets.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.sets.union-difference $p |- ( ( A e. _V /\ B e. _V ) -> ( A u. ( B \ A ) ) = ( A u. B ) ) $=
    ( cdif cun wceq cvv wcel wa undif2 a1i ) ABACDABDEAFGBFGHABIJ $.
$}
