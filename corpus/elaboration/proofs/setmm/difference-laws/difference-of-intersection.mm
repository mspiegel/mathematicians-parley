$( proofs/setmm/difference-laws/difference-of-intersection, elaborated from proofs/setmm/difference-laws.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d k m $.
  $d A k m $.
  $d B k m $.
  proofs.setmm.difference-laws.difference-of-intersection $p |- ( ( A e. _V /\ B e. _V ) -> ( A \ ( A i^i B ) ) = ( A \ B ) ) $=
    ( cvv wcel wa cin cdif wss wceq vm cv wral wn simpr wb eldif a1i mpbid simpld simpl syl jca elin mpbird pm2.21dd ex pm2.01d ralrimiva dfss3 vk simprd eqss sylibr ) ACDZBCDZEZAABFZGZABGZHZUSURHZEURUSIUPUTVAUPUTJKZUSDZJURLZUPVCJURUPVBURDZEZVCVBADZVBBDZMZEZVFVGVIVFVGVBUQDZMZVFVEVGVLEZUPVENZVEVMOZVFVBAUQPZQZRZSVFVHVFVHVIVFVHEZVKVIVSVKVGVHEZVSVGVHVSVGVLVSVFVMVFVHTZVRUAZSVFVHNUBVKVTOVSVBABUCQUDVSVMVLWBVGVLNUAUEUFUGUBVCVJOVFVBABPQUDUHUTVDOUPJURUSUIQUDUPVAUJKZURDZUJUSLZUPWDUJUSUPWCUSDZEZWDWCADZWCUQDZMZEZWGWHWJWGWHWCBDZMZWGWFWHWMEZUPWFNZWFWNOZWGWCABPZQZRZSWGWIWGWIWJWGWIEZWLWJWTWHWLWTWIWHWLEZWGWINWIXAOWTWCABUCQRUKWTWNWMWTWGWNWGWITWSUAWHWMNUAUEUFUGUBWDWKOWGWCAUQPQUDUHVAWEOUPUJUSURUIQUDUBURUSULUM $.
$}
