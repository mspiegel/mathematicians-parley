$( tests/elaborator/a-range-a-function-is-typed-over/a-range-a-function-is-typed-over, elaborated from tests/elaborator/a-range-a-function-is-typed-over.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.a-range-a-function-is-typed-over.a-range-a-function-is-typed-over $p |- ( ( ( A e. NN /\ B : ( 1 ... A ) --> RR ) /\ C e. ( 1 ... A ) ) -> ( B ` C ) e. RR ) $=
    ( cn wcel c1 cfz co cr wf wa cfv simpl simpr syl jca ffvelcdm ) ADEZFAGHZIBJZKZCSEZKZTUBKCBLIEUCTUBUCUATUAUBMRTNOUAUBNPSICBQO $.
$}
