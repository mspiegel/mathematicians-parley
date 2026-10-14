$( tests/elaborator/a-type-a-line-states/a-type-a-line-states-required, elaborated from tests/elaborator/a-type-a-line-states.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.a-type-a-line-states.a-type-a-line-states-required $p |- ( ( ( ( ( A e. _V /\ B e. _V ) /\ C Fn A ) /\ C : A --> B ) /\ D e. A ) -> ( C ` D ) e. B ) $=
    ( cvv wcel wa wfn wf cfv simpl simpr syl jca ffvelcdm ) AEFZBEFZGZCAHZGZABCIZGZDAFZGZUAUCGDCJBFUDUAUCUDUBUAUBUCKTUALMUBUCLNABDCOM $.
$}
