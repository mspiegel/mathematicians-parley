$( tests/elaborator/textbook-exercise-shapes/a-definition-unfolding-the-second-sentence, elaborated from tests/elaborator/textbook-exercise-shapes.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d m n $.
  $d A m n $.
  tests.elaborator.textbook-exercise-shapes.a-definition-unfolding-the-second-sentence $p |- ( A e. ( ran ( n e. ZZ |-> ( 2 x. n ) ) i^i ran ( n e. ZZ |-> ( 3 x. n ) ) ) -> E. n e. ZZ A = ( 3 x. n ) ) $=
    ( cz c2 cv cmul co cmpt crn c3 cin wcel wceq wrex wa id wb elin a1i mpbid simpr syl cvv wral vm ovex ralrimiva oveq2d eleq1d cbvralvw sylib eqid elrnmptg ) ABCDBEZFGZHZIZBCJUNFGZHZIZKZLZAUTLZAURMZBCNZVBAUQLZVCOZVCVBVBVGVBPVBVGQVBAUQUTRSTVFVCUAUBVBURUCLZBCUDZVCVEQVBJUEEZFGZUCLZUECUDVIVBVLUECVLVBVJCLOJVJFUFSUGVLVHUEBCVJUNMZVKURUCVMVJUNJFVMPUHUIUJUKBCURAUSUCUSULUMUBT $.
$}
