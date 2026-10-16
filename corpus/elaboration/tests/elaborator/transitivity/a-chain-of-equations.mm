$( tests/elaborator/transitivity/a-chain-of-equations, elaborated from tests/elaborator/transitivity.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.transitivity.a-chain-of-equations $p |- ( ( ( ( ( A e. _V /\ B e. _V ) /\ C e. _V ) /\ A = B ) /\ B = C ) -> A = C ) $=
    ( cvv wcel wa wceq simpl simpr syl eqtrd ) ADEZBDEZFZCDEZFZABGZFZBCGZFZABCTRQRSHPQIJRSIK $.
$}
