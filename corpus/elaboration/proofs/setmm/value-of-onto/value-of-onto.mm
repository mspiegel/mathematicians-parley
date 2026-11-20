$( proofs/setmm/value-of-onto/value-of-onto, elaborated from proofs/setmm/value-of-onto.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d k m x $.
  $d A k m x $.
  $d B k m x $.
  $d C k m x $.
  $d D k m x $.
  proofs.setmm.value-of-onto.value-of-onto $p |- ( ( ( ( ( A e. _V /\ B e. _V ) /\ C : A --> B ) /\ ( C " A ) = B ) /\ D e. B ) -> E. x e. A D = ( C ` x ) ) $=
    ( cvv wcel wa wf cima wceq vm cv cfv wrex simpr simpl syl eqcomd eleq2d mpbid wss wb ssid a1i jca gfvelima vk id fveq2d eqeq2d cbvrexvw bitri rspcev ex rexlimdva mpd ) BFGZCFGZHZBCDIZHZDBJZCKZHZECGZHZELMZDNZKZLBOZEAMZDNZKZABOZVGVOVKVGEVCGZVOVGVFVPVEVFPVGCVCEVGVCCVGVEVDVEVFQZVBVDPRSTUAVGVABBUBZHVPVOUCVGVAVRVGVEVAVQVEVBVAVBVDQUTVAPRRVRVGBUDUEUFABCEBDUGRUAVOVKUCVGVOEUHMZDNZKZUHBOVKVNWAAUHBVLVSKZVMVTEWBVLVSDWBUIUJUKULWAVJUHLBVSVHKZVTVIEWCVSVHDWCUIUJUKULUMUEUAVGVJVOLBVGVHBGZHZVJVOWEVJHZWDVJHVOWFWDVJWFWEWDWEVJQVGWDPRWEVJPUFVNVJAVHBVLVHKZVMVIEWGVLVHDWGUIUJUKUNRUOUPUQ $.
$}
