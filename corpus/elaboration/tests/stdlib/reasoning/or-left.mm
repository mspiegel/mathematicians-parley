$( tests/stdlib/reasoning/or-left, elaborated from tests/stdlib/reasoning.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.reasoning.or-left $p |- ( ( A e. RR /\ A = 0 ) -> ( A = 0 \/ A = 1 ) ) $=
    ( cr wcel cc0 wceq wa c1 wo simpr orc syl ) ABCZADEZFMMAGEZHLMIMNJK $.
$}
