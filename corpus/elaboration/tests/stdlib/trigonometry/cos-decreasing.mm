$( tests/stdlib/trigonometry/cos-decreasing, elaborated from tests/stdlib/trigonometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.trigonometry.cos-decreasing $p |- ( ( A e. ( 0 [,] _pi ) /\ B e. ( 0 [,] _pi ) ) -> ( A < B <-> ( cos ` B ) < ( cos ` A ) ) ) $=
    ( cosord ) ABC $.
$}
