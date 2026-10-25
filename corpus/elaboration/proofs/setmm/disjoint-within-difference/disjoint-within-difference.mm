$( proofs/setmm/disjoint-within-difference/disjoint-within-difference, elaborated from proofs/setmm/disjoint-within-difference.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d k m t $.
  $d A k m t $.
  $d B k m t $.
  $d C k m t $.
  proofs.setmm.disjoint-within-difference.disjoint-within-difference $p |- ( ( ( ( A e. _V /\ B e. _V ) /\ C e. _V ) /\ A C_ C ) -> ( ( A i^i B ) = (/) <-> A C_ ( C \ B ) ) ) $=
    ( cvv wcel wa wss cin c0 wceq cdif vm cv wral wn simpl simpr syl jca ssel2 disjel wb eldif a1i mpbird ralrimiva dfss3 incom vk vt mpbid wi id eleq1d rspcv mpd simprd disjr sylibr eqtrd impbida ) ADEZBDEZFZCDEZFZACGZFZABHZIJZACBKZGZVHVJFZVLLMZVKEZLANZVMVOLAVMVNAEZFZVOVNCEZVNBEZOZFZVRVSWAVRVGVQFVSVRVGVQVRVMVGVMVQPZVMVHVGVHVJPVFVGQRRVMVQQZSACVNTRVRVJVQFWAVRVJVQVRVMVJWCVHVJQRWDSABVNUARSVOWBUBVRVNCBUCUDUEUFVLVPUBVMLAVKUGUDUEVHVLFZVIBAHZIVIWFJWEABUHUDWEUIMZBEZOZUIANWFIJWEWIUIAWEWGAEZFZWGCEZWIWKWGVKEZWLWIFZWKUJMZVKEZUJANZWMWKWQWMFWQWKWQWMWKWEWQWEWJPZWEVLWQVHVLQZVLWQUBZWEUJAVKUGZUDZUKZRZWKWQWMXDWKWJWQWMULZWEWJQZWPWMUJWGAWOWGJZWOWGVKXGUMZUNZUOZRZUPSWQWMPRXKUPWMWNUBWKWGCBUCUDUKUQUFUIBAURUSUTVA $.
$}
