$( tests/elaborator/reading-sentences/a-second-sentence-substituted-into, elaborated from tests/elaborator/reading-sentences.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.reading-sentences.a-second-sentence-substituted-into $p |- ( ( ( ( A e. RR /\ B e. RR ) /\ ( A = 1 /\ A < B ) ) /\ B = 2 ) -> A < 2 ) $=
    ( cr wcel wa c1 wceq clt wbr c2 simpl simpr syl breq2d mpbid ) ACDZBCDZEZAFGZABHIZEZEZBJGZEZTAJHIUDUATUDUBUAUBUCKRUALMSTLMUDBJAHUBUCLNO $.
$}
