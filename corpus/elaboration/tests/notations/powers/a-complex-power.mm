$( tests/notations/powers/a-complex-power, elaborated from tests/notations/powers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.notations.powers.a-complex-power $p |- ( ( A e. CC /\ B e. CC ) -> ( A ^c B ) e. CC ) $=
    ( cxpcl ) ABC $.
$}
