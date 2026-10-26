$( tests/stdlib/calculus/an-integral-not-negative, elaborated from tests/stdlib/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d k m s y $.
  $d A k m s y $.
  $d B k m s y $.
  $d C k m s y $.
  tests.stdlib.calculus.an-integral-not-negative $p |- ( ( ( ( ( ( A e. RR /\ B e. RR ) /\ A < B ) /\ C : ( A [,] B ) --> RR ) /\ A. y e. ( A [,] B ) 0 <_ ( C ` y ) ) /\ ( C |` ( A [,] B ) ) e. ( ( A [,] B ) -cn-> RR ) ) -> 0 <_ S_ [ A -> B ] ( C ` s ) _d s ) $=
    ( cr wcel wa clt wbr cicc co wf cc0 cv cfv cle wral cres ccncf vm simpl id syl simpr wb vk wceq fveq2d breq2d cbvralvw bitri a1i mpbid gditgge0res ) BFGZCFGZHZBCIJZHZBCKLZFDMZHZNAOZDPZQJZAVARZHZDVASZVAFTLZGZHZUAEBCDVLVHUPVHVKUBZVHVCUPVCVGUBZVCUTUPUTVBUBZUTURUPURUSUBZURUPUPUPUQUBUPUCUDUDUDUDUDVLVHUQVMVHVCUQVNVCUTUQVOUTURUQVPUPUQUEUDUDUDUDVLVHUSVMVHVCUSVNVCUTUSVOURUSUEUDUDUDVLVHVBVMVHVCVBVNUTVBUEUDUDVLVGNUAOZDPZQJZUAVARZVLVHVGVMVCVGUEUDVGVTUFVLVGNUGOZDPZQJZUGVARVTVFWCAUGVAVDWAUHZVEWBNQWDVDWADWDUCUIUJUKWCVSUGUAVAWAVQUHZWBVRNQWEWAVQDWEUCUIUJUKULUMUNVHVKUEUO $.
$}
