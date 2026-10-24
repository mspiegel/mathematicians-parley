$( tests/elaborator/a-function-type-widened/a-function-type-widened, elaborated from tests/elaborator/a-function-type-widened.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A k $.
  $d B k $.
  tests.elaborator.a-function-type-widened.a-function-type-widened $p |- ( ( A e. NN /\ B : ( 1 ... A ) --> NN ) -> prod_ k e. ( 1 ... A ) ( B ` k ) e. RR ) $=
    ( cn wcel c1 cfz co wf wa cv cfv cfn fzfi a1i cr simpl simpr syl jca ffvelcdm nnre fprodrecl ) ADEZFAGHZDBIZJZUECKZBLZCUEMEUGFANOUGUHUEEZJZUIDEZUIPEUKUFUJJULUKUFUJUKUGUFUGUJQUDUFRSUGUJRTUEDUHBUASUIUBSUC $.
$}
