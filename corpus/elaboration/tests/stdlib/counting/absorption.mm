$( tests/stdlib/counting/absorption, elaborated from tests/stdlib/counting.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.counting.absorption $p |- ( ( A e. NN0 /\ B e. ( 0 ... A ) ) -> ( ( A + 1 ) _C ( B + 1 ) ) = ( ( A _C B ) x. ( ( A + 1 ) / ( B + 1 ) ) ) ) $=
    ( cn0 wcel cc0 cfz co wa c1 caddc cbc cdiv cmul wceq simpr bcp1nk syl ) ACDZBEAFGZDZHTAIJGZBIJGZKGABKGUAUBLGMGNRTOBAPQ $.
$}
