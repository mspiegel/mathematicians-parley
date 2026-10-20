$( proofs/hammack/powers-of-two-onto/powers-of-two-onto, elaborated from proofs/hammack/powers-of-two-onto.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d j k n x $.
  $d A j k n x $.
  proofs.hammack.powers-of-two-onto.powers-of-two-onto $p |- ( ( A : ZZ --> ran ( n e. ZZ |-> ( 2 ^ n ) ) /\ A. n e. ZZ ( A ` n ) = ( 2 ^ n ) ) -> A : ZZ -onto-> ran ( n e. ZZ |-> ( 2 ^ n ) ) ) $=
    ( cz c2 cv cexp co cmpt crn wf cfv wceq wral wa wfo vk vx wrex simpl id syl wcel vj simpr cvv wb ovex a1i ralrimiva oveq2d eleq1d cbvralvw sylib eqid elrnmptg mpbid eqeq2d cbvrexvw wi fveq2d eqeq12d rspcv mpd eqcomd eqtrd jca rspcev ex rexlimdva dffo3 mpbird ) CBCDBEZFGZHZIZAJZVLAKZVMLZBCMZNZCVOAOZVPPEZQEZAKZLZQCRZPVOMZNZVTVPWGVTVPVPVPVSSVPTUAVTWFPVOVTWBVOUBZNZWBDUCEZFGZLZUCCRZWFWJWBVMLZBCRZWNWJWIWPVTWIUDWJVMUEUBZBCMZWIWPUFWJWLUEUBZUCCMWRWJWSUCCWSWJWKCUBZNZDWKFUGUHUIWSWQUCBCWKVLLZWLVMUEXBWKVLDFXBTUJUKULUMBCVMWBVNUEVNUNUOUAUPWPWNUFWJWOWMBUCCVLWKLZVMWLWBXCVLWKDFXCTZUJZUQURUHUPWJWMWFUCCXAWMWFXAWMNZWTWBWKAKZLZNWFXFWTXHXFXAWTXAWMSZWJWTUDZUAZXFWBWLXGXAWMUDXFXGWLXFVSXGWLLZXFXAVSXIXAWJVSWJWTSWJVTVSVTWISVPVSUDUAUAUAXFWTVSXLUSXKVRXLBWKCXCVQXGVMWLXCVLWKAXDUTXEVAVBUAVCVDVEVFWEXHQWKCWCWKLZWDXGWBXMWCWKAXMTUTUQVGUAVHVIVCUIVFWAWHUFVTQPCVOAVJUHVK $.
$}
