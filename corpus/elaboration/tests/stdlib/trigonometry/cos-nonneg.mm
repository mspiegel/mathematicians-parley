$( tests/stdlib/trigonometry/cos-nonneg, elaborated from tests/stdlib/trigonometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.trigonometry.cos-nonneg $p |- ( A e. ( -u ( _pi / 2 ) [,] ( _pi / 2 ) ) -> 0 <_ ( cos ` A ) ) $=
    ( cosq14ge0 ) AB $.
$}
