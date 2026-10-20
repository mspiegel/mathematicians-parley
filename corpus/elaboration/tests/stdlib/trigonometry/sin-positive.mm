$( tests/stdlib/trigonometry/sin-positive, elaborated from tests/stdlib/trigonometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.trigonometry.sin-positive $p |- ( A e. ( 0 (,) _pi ) -> 0 < ( sin ` A ) ) $=
    ( sinq12gt0 ) AB $.
$}
