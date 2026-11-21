$( tests/stdlib/calculus/integral-over-a-point, elaborated from tests/stdlib/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d m s t $.
  $d A m s t $.
  $d B m s t $.
  tests.stdlib.calculus.integral-over-a-point $p |- ( ( A e. RR /\ B : RR --> RR ) -> S_ [ A -> A ] ( B ` s ) _d s = 0 ) $=
    ( cr wcel wf wa vt cv cfv cdit cc0 wceq ditg0 a1i wb vm id fveq2d cbvditgv eqeq1i bitri mpbid ) ADEZDDBFZGZHAAHIZBJZKZLMZCAACIZBJZKZLMZUJUFHAUHNOUJUNPUFUJQAAQIZBJZKZLMUNUIUQLHQAAUHUPUGUOMZUGUOBURRSTUAUQUMLQCAAUPULUOUKMZUOUKBUSRSTUAUBOUC $.
$}
