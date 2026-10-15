$( proofs/setmm/onto-bijection-reaches-all/onto-bijection-reaches-all, elaborated from proofs/setmm/onto-bijection-reaches-all.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/setmm/value-of-onto/value-of-onto.mm $]

${
  $d j k m x y $.
  $d A j k m x y $.
  $d B j k m x y $.
  $d C j k m x y $.
  proofs.setmm.onto-bijection-reaches-all.onto-bijection-reaches-all $p |- ( ( ( ( A e. _V /\ B e. _V ) /\ ( C : A --> B /\ C : A -1-1-> B ) ) /\ ( C " A ) = B ) -> A. y e. B E. x e. A y = ( C ` x ) ) $=
    ( cvv wcel wa wf wf1 cima wceq vm cv cfv wrex wral simpl id syl simpr jca proofs.setmm.value-of-onto.value-of-onto ralrimiva wb vk vj fveq2d eqeq2d cbvrexvw ralbii eqeq1d rexbidva cbvralvw bitri a1i mpbid ) CFGZDFGZHZCDEIZCDEJZHZHZECKZDLZHZMNZANZEOZLZACPZMDQZBNZVJLZACPZBDQZVGVLMDVGVHDGZHZUTVAHZVFHZVRHVLVSWAVRVSVTVFVSUTVAVSURUSVSVGURVGVRRZVGVDURVDVFRZVDUTURUTVCRZUTURURURUSRURSTTTTVSVGUSWBVGVDUSWCVDUTUSWDURUSUATTTUBVSVGVAWBVGVCVAVGVDVCWCUTVCUATVAVBRTTUBVSVGVFWBVDVFUATUBVGVRUAUBACDEVHUCTUDVMVQUEVGVMUFNZUGNZEOZLZUGCPZUFDQZVQVMVHWGLZUGCPZMDQWJVLWLMDVKWKAUGCVIWFLZVJWGVHWMVIWFEWMSUHUIUJUKWLWIMUFDVHWELZWKWHUGCWNWFCGZHZVHWEWGWPWNWNWNWORWNSTULUMUNUOWJWEVJLZACPZUFDQVQWIWRUFDWHWQUGACWFVILZWGVJWEWSWFVIEWSSUHUIUJUKWRVPUFBDWEVNLZWQVOACWTVICGZHZWEVNVJXBWTWTWTXARWTSTULUMUNUOUOUPUQ $.
$}
