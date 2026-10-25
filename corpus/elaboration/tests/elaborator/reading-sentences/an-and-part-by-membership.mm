$( tests/elaborator/reading-sentences/an-and-part-by-membership, elaborated from tests/elaborator/reading-sentences.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.reading-sentences.an-and-part-by-membership $p |- ( ( ( A e. RR /\ B e. RR ) /\ ( A = 1 /\ ( sqrt ` B ) e. RR ) ) -> ( ( sqrt ` B ) + 1 ) e. RR ) $=
    ( cr wcel wa c1 wceq csqrt cfv simpr syl 1re a1i readdcld ) ACDZBCDZEZAFGZBHIZCDZEZEZSFUBUATQUAJRTJKFCDUBLMN $.
$}
