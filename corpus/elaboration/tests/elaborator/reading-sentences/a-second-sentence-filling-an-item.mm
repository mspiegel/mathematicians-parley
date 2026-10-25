$( tests/elaborator/reading-sentences/a-second-sentence-filling-an-item, elaborated from tests/elaborator/reading-sentences.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.reading-sentences.a-second-sentence-filling-an-item $p |- ( ( ( A e. RR /\ B e. RR ) /\ ( A = 1 /\ B = 2 ) ) -> ( B = 0 \/ B = 2 ) ) $=
    ( cr wcel wa c1 wceq c2 cc0 wo simpr syl olc ) ACDZBCDZEZAFGZBHGZEZEZRBIGZRJTSRPSKQRKLRUAML $.
$}
