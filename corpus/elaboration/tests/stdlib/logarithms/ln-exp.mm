$( tests/stdlib/logarithms/ln-exp, elaborated from tests/stdlib/logarithms.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.logarithms.ln-exp $p |- ( A e. RR -> ( log ` ( exp ` A ) ) = A ) $=
    ( cr wcel ce cfv clog wceq id relogef syl ) ABCZKADEFEAGKHAIJ $.
$}
