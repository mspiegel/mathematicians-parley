$( tests/notations/powers/a-half-power, elaborated from tests/notations/powers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.notations.powers.a-half-power $p |- ( A e. RR -> ( A ^c ( 1 / 2 ) ) = ( sqrt ` A ) ) $=
    ( cr wcel cc c1 c2 cdiv co ccxp csqrt cfv wceq id recn syl cxpsqrt ) ABCZADCZAEFGHIHAJKLQQRQMANOAPO $.
$}
