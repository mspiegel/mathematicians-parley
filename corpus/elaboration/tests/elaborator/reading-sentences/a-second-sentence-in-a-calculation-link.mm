$( tests/elaborator/reading-sentences/a-second-sentence-in-a-calculation-link, elaborated from tests/elaborator/reading-sentences.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.reading-sentences.a-second-sentence-in-a-calculation-link $p |- ( ( ( A e. RR /\ B e. RR ) /\ ( A = 1 /\ B = 2 ) ) -> B = ( 1 + 1 ) ) $=
    ( cr wcel wa c1 wceq c2 caddc co simpr syl eqid oveq12i 1p1e2 eqtri eqtr4i a1i eqtrd ) ACDZBCDZEZAFGZBHGZEZEZBHFFIJZUFUEUDUBUEKUCUDKLHUGGUFHHUGHMUGUGHFFFFIFMZUHNOPQRS $.
$}
