$( tests/elaborator/sets-a-define-names/values-in-a-range, elaborated from tests/elaborator/sets-a-define-names.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.sets-a-define-names.values-in-a-range $p |- ( ( ( ( A e. NN /\ B e. NN ) /\ C : ( 1 ... A ) --> ( 1 ... B ) ) /\ D e. ( 1 ... A ) ) -> ( C ` D ) <_ ( C ` D ) ) $=
    ( cn wcel wa c1 cfz co wf cfv cr simpl simpr syl ffvelcdm syl2anc elfznn nnre leidd ) AEFZBEFZGZHAIJZHBIJZCKZGZDUEFZGZDCLZUJUKEFZUKMFUJUKUFFZULUJUGUIUMUJUHUGUHUINUDUGOPUHUIOUEUFDCQRUKBSPUKTPUA $.
$}
