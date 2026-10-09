$( tests/stdlib/calculus/integral-over-a-point, elaborated from tests/stdlib/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A s $.
  $d B s $.
  tests.stdlib.calculus.integral-over-a-point $p |- ( ( A e. RR /\ B : RR --> RR ) -> S_ [ A -> A ] ( B ` s ) _d s = 0 ) $=
    ( cv cfv cdit cc0 wceq cr wcel wf wa ditg0 a1i ) CAACDZBEZFGHAIJIIBKLCAPMN $.
$}
