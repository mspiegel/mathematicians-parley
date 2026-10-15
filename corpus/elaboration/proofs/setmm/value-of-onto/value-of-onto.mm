$( proofs/setmm/value-of-onto/value-of-onto, elaborated from proofs/setmm/value-of-onto.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d m x $.
  $d A m x $.
  $d B m x $.
  $d C m x $.
  $d D m x $.
  proofs.setmm.value-of-onto.value-of-onto $p |- ( ( ( ( ( A e. _V /\ B e. _V ) /\ C : A --> B ) /\ ( C " A ) = B ) /\ D e. B ) -> E. x e. A D = ( C ` x ) ) $=
    ( cvv wcel wa wf cima wceq vm cv cfv wrex simpr simpl syl eqcomd eleq2d mpbid wss wb ssid a1i jca gfvelima id fveq2d eqeq2d rspcev ex rexlimdva mpd ) BFGZCFGZHZBCDIZHZDBJZCKZHZECGZHZELMZDNZKZLBOZEAMZDNZKZABOZVDEUTGZVHVDVCVMVBVCPVDCUTEVDUTCVDVBVAVBVCQZUSVAPRSTUAVDURBBUBZHVMVHUCVDURVOVDVBURVNVBUSURUSVAQUQURPRRVOVDBUDUEUFLBCEBDUGRUAVDVGVLLBVDVEBGZHZVGVLVQVGHZVPVGHVLVRVPVGVRVQVPVQVGQVDVPPRVQVGPUFVKVGAVEBVIVEKZVJVFEVSVIVEDVSUHUIUJUKRULUMUN $.
$}
