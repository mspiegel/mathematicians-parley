$( tests/elaborator/a-set-image-from-an-equation/a-set-image-from-an-equation, elaborated from tests/elaborator/a-set-image-from-an-equation.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d k n $.
  $d A k n $.
  $d B k n $.
  tests.elaborator.a-set-image-from-an-equation.a-set-image-from-an-equation $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ B = ( 2 x. A ) ) -> B e. ran ( n e. ZZ |-> ( 2 x. n ) ) ) $=
    ( cz wcel wa c2 cmul co wceq cv cmpt crn vk wrex simpl id syl simpr jca oveq2d eqeq2d rspcev cvv wral wb ovex a1i ralrimiva cbvmptv elrnmptg mpbird ) ADEZBDEZFZBGAHIZJZFZBCDGCKZHIZLZMZEZBGNKZHIZJZNDOZURUMUQFVGURUMUQURUOUMUOUQPUOUMUMUMUNPUMQRRUOUQSTVFUQNADVDAJZVEUPBVHVDAGHVHQUAUBUCRURVEUDEZNDUEVCVGUFURVINDVIURVDDEFGVDHUGUHUINDVEBVAUDCNDUTVEUSVDJZUSVDGHVJQUAUJUKRUL $.
$}
