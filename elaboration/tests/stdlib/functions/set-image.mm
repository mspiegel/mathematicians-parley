$( tests/stdlib/functions/set-image, elaborated from tests/stdlib/functions.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A s $.
  $d B s $.
  $d C s $.
  $d D s $.
  setimage $p |- ( ( ( ( ( A e. _V /\ B e. _V ) /\ C : A --> B ) /\ D e. _V ) /\ D e. ran ( s e. A |-> ( C ` s ) ) ) -> E. s e. A D = ( C ` s ) ) $=
    ( cvv wcel wa wf cv cfv cmpt crn wceq wrex simpr wral wb fvex a1i rgen eqid elrnmptg syl mpbid ) AFGZBFGZHZABCIZHZDFGZHZDEAEJZCKZLZMZGZHZUQDUNNZEAOZULUQPURUNFGZEAQZUQUTRVBURVAEAVAUMAGUMCSTUATEAUNDUOFUOUBUCUDUE $.
$}
