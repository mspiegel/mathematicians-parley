$( tests/stdlib/calculus/closed-between-two-inner-points, elaborated from tests/stdlib/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.calculus.closed-between-two-inner-points $p |- ( ( ( ( A e. RR /\ B e. RR ) /\ C e. ( A (,) B ) ) /\ D e. ( A (,) B ) ) -> ( C [,] D ) C_ ( A (,) B ) ) $=
    ( cr wcel wa cioo co cicc wss simpl simpr syl jca iccssioo2 ) AEFZBEFZGZCABHIZFZGZDTFZGZUAUCGCDJITKUDUAUCUDUBUAUBUCLSUAMNUBUCMOABCDPN $.
$}
