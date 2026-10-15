$( proofs/setmm/difference-laws/intersection-with-difference, elaborated from proofs/setmm/difference-laws.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d k m $.
  $d A k m $.
  $d B k m $.
  proofs.setmm.difference-laws.intersection-with-difference $p |- ( ( A e. _V /\ B e. _V ) -> ( A i^i ( A \ B ) ) = ( A \ B ) ) $=
    ( cvv wcel wa cdif cin wss wceq vm cv wral simpr wb elin a1i mpbid simprd ralrimiva dfss3 mpbird vk wn eldif simpld jca eqss sylibr ) ACDZBCDZEZAABFZGZULHZULUMHZEUMULIUKUNUOUKUNJKZULDZJUMLZUKUQJUMUKUPUMDZEZUPADZUQUTUSVAUQEZUKUSMUSVBNUTUPAULOPQRSUNURNUKJUMULTPUAUKUOUBKZUMDZUBULLZUKVDUBULUKVCULDZEZVDVCADZVFEZVGVHVFVGVHVCBDZUCZVGVFVHVKEZUKVFMZVFVLNVGVCABUDPQUEVMUFVDVINVGVCAULOPUASUOVENUKUBULUMTPUAUFUMULUGUH $.
$}
