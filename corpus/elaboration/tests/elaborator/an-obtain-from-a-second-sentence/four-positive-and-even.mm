$( tests/elaborator/an-obtain-from-a-second-sentence/four-positive-and-even, elaborated from tests/elaborator/an-obtain-from-a-second-sentence.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.an-obtain-from-a-second-sentence.four-positive-and-even $p |- ( 0 < 4 /\ E. k e. ZZ 4 = ( 2 x. k ) ) $=
    ( cc0 c4 clt wbr c2 cv cmul co wceq cz wrex wa wtru 4pos a1i wcel 2z eqid oveq12i 2t2e4 eqtri eqtr4i jca id oveq2d eqeq2d rspcev syl mptru ) BCDEZCFAGZHIZJZAKLZMNUKUOUKNOPNFKQZCFFHIZJZMUONUPURUPNRPURNCCUQCSUQUQCFFFFHFSZUSTUAUBUCPUDUNURAFKULFJZUMUQCUTULFFHUTUEUFUGUHUIUDUJ $.
$}
