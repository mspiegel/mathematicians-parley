$( proofs/setmm/size-without-a-pair/size-without-a-pair, elaborated from proofs/setmm/size-without-a-pair.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/setmm/size-of-difference/size-of-difference.mm $]

${
  proofs.setmm.size-without-a-pair.size-without-a-pair $p |- ( ( ( ( ( A e. _V /\ B e. A ) /\ C e. A ) /\ A e. Fin ) /\ -. B = C ) -> ( # ` ( A \ { B , C } ) ) = ( ( # ` A ) - 2 ) ) $=
    ( cvv wcel wa cfn wceq wn cpr cdif chash cfv cmin co c2 wss simpl id syl prex a1i jca simpr prssi proofs.setmm.size-of-difference.size-of-difference wne neqcomd wb df-ne eqcom bicomd notbid bitrd mpbid elex hashprg oveq2d eqeq2d ) ADEZBAEZFZCAEZFZAGEZFZBCHZIZFZABCJZKZLMZALMZVJLMZNOZHZVLVMPNOZHVIUTVJDEZFZVEFZVJAQZFVPVIVTWAVIVSVEVIUTVRVIVFUTVFVHRZVFVDUTVDVERZVDVBUTVBVCRZVBUTUTUTVARUTSTTTTVRVIBCUAUBUCVIVFVEWBVDVEUDTUCVIVAVCFWAVIVAVCVIVFVAWBVFVDVAWCVDVBVAWDUTVAUDZTZTZTZVIVFVCWBVFVDVCWCVBVCUDZTZTZUCBCAUETUCAVJUFTVIVOVQVLVIVNPVMNVIBCUGZVNPHZVICBHZIZWLVIBCVFVHUDUHVIWLWOVIWLVHWOWLVHUIVIBCUJUBVIVGWNVIWNVGWNVGUIVICBUKUBULUMUNULUOVIBDEZCDEZFWLWMUIVIWPWQVIVAWPWHBAUPTVIVCWQWKCAUPTUCBCDDUQTUOURUSUO $.
$}
