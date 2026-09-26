$( tests/stdlib/functions/set-image, elaborated from tests/stdlib/functions.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d m s $.
  $d A m s $.
  $d B m s $.
  $d C m s $.
  $d D m s $.
  setimage $p |- ( ( ( ( ( A e. _V /\ B e. _V ) /\ C : A --> B ) /\ D e. _V ) /\ D e. ran ( s e. A |-> ( C ` s ) ) ) -> E. s e. A D = ( C ` s ) ) $=
    ( cvv wcel wa wf cv cfv cmpt crn wceq wrex simpr wral wb vm fvex a1i ralrimiva id fveq2d eleq1d cbvralvw sylib eqid elrnmptg syl mpbid ) AFGZBFGZHZABCIZHZDFGZHZDEAEJZCKZLZMZGZHZVCDUTNZEAOZURVCPVDUTFGZEAQZVCVFRVDSJZCKZFGZSAQVHVDVKSAVKVDVIAGHVICTUAUBVKVGSEAVIUSNZVJUTFVLVIUSCVLUCUDUEUFUGEAUTDVAFVAUHUIUJUK $.
$}
