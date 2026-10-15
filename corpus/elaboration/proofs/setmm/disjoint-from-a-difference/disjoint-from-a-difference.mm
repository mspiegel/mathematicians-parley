$( proofs/setmm/disjoint-from-a-difference/disjoint-from-a-difference, elaborated from proofs/setmm/disjoint-from-a-difference.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A m $.
  $d B m $.
  $d C m $.
  proofs.setmm.disjoint-from-a-difference.disjoint-from-a-difference $p |- ( ( ( ( A e. _V /\ B e. _V ) /\ C e. _V ) /\ ( ( A \ B ) i^i C ) = (/) ) -> ( C C_ A -> C C_ B ) ) $=
    ( cvv wcel wa cdif cin c0 wceq wss vm cv wral wn simpl simpr syl jca ssel2 wb eldif a1i mpbird disjel pm2.21dd ex pm2.18d ralrimiva dfss3 ) ADEZBDEZFZCDEZFZABGZCHZIJZFZCAKZCBKZUSUTFZVALMZBEZLCNZVBVDLCVBVCCEZFZVDVGVDOZVDVGVHFZVFVDVIVGVFVGVHPZVBVFQZRVIURVCUPEZFVFOVIURVLVIVGURVJVGVBURVBVFPZVBUSURUSUTPUOURQRRRVIVLVCAEZVHFZVIVNVHVIVGVNVJVGUTVFFVNVGUTVFVGVBUTVMUSUTQRVKSCAVCTRRVGVHQSVLVOUAVIVCABUBUCUDSUPCVCUERUFUGUHUIVAVEUAVBLCBUJUCUDUG $.
$}
