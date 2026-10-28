$( proofs/setmm/difference-inside-a-larger-set/difference-inside-a-larger-set, elaborated from proofs/setmm/difference-inside-a-larger-set.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/sets/subset-antisymmetric.mm $]

${
  $d k m $.
  $d A k m $.
  $d B k m $.
  $d C k m $.
  proofs.setmm.difference-inside-a-larger-set.difference-inside-a-larger-set $p |- ( ( ( ( A e. _V /\ B e. _V ) /\ C e. _V ) /\ A C_ C ) -> ( A \ B ) = ( ( C \ B ) i^i A ) ) $=
    ( cvv wcel wa wss cdif cin wceq simpl id syl difexg simpr inex1g jca vm cv wral wn wb eldif a1i mpbid ssel2 mpbird elin ralrimiva dfss3 vk stdlib.sets.subset-antisymmetric ) ADEZBDEZFZCDEZFZACGZFZABHZDEZCBHZAIZDEZFZUTVCGZFZVCUTGZFUTVCJUSVGVHUSVEVFUSVAVDUSUMVAUSUQUMUQURKZUQUOUMUOUPKUOUMUMUMUNKUMLMMMABDNMUSVBDEZVDUSUPVJUSUQUPVIUOUPOMCBDNMVBADPMQUSVFRSZVCEZRUTTZUSVLRUTUSVKUTEZFZVLVKVBEZVKAEZFZVOVPVQVOVPVKCEZVKBEZUAZFZVOVSWAVOURVQFVSVOURVQVOUSURUSVNKUQUROMVOVQWAFZVQVOVNWCUSVNOZVNWCUBZVOVKABUCZUDZUEZVQWAKZMZQACVKUFMVOWCWAWHVQWAOMQVPWBUBVOVKCBUCUDUGWJQVLVRUBVOVKVBAUHUDUGUIVFVMUBUSRUTVCUJUDUGQUSVHUKSZUTEZUKVCTZUSWLUKVCUSWKVCEZFZWLWKAEZWKBEZUAZFZWOWPWRWOWKVBEZWPFZWPWOWNXAUSWNOZWNXAUBZWOWKVBAUHZUDZUEZWTWPOMWOWKCEZWRFZWRWOWTXHWOXAWTXFWTWPKMWTXHUBWOWKCBUCUDUEXGWROMQWLWSUBWOWKABUCUDUGUIVHWMUBUSUKVCUTUJUDUGQUTVCULM $.
$}
