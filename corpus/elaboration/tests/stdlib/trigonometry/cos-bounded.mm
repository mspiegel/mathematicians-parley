$( tests/stdlib/trigonometry/cos-bounded, elaborated from tests/stdlib/trigonometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.trigonometry.cos-bounded $p |- ( A e. RR -> ( -u 1 <_ ( cos ` A ) /\ ( cos ` A ) <_ 1 ) ) $=
    ( cr wcel c1 cneg ccos cfv cle wbr wa id cosbnd syl ) ABCZNDEAFGZHIODHIJNKALM $.
$}
