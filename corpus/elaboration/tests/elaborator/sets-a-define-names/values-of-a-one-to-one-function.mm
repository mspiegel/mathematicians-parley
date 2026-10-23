$( tests/elaborator/sets-a-define-names/values-of-a-one-to-one-function, elaborated from tests/elaborator/sets-a-define-names.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.sets-a-define-names.values-of-a-one-to-one-function $p |- ( ( ( A e. NN /\ ( B : ( 1 ... A ) --> RR /\ B : ( 1 ... A ) -1-1-> RR ) ) /\ C e. ( 1 ... A ) ) -> ( B ` C ) <_ ( B ` C ) ) $=
    ( cn wcel c1 cfz co cr wf wf1 wa cfv simpl simpr syl ffvelcdm syl2anc leidd ) ADEZFAGHZIBJZUAIBKZLZLZCUAEZLZCBMZUGUBUFUHIEUGUDUBUGUEUDUEUFNTUDOPUBUCNPUEUFOUAICBQRS $.
$}
