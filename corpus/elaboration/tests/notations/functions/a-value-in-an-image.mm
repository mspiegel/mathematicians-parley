$( tests/notations/functions/a-value-in-an-image, elaborated from tests/notations/functions.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A x $.
  tests.notations.functions.a-value-in-an-image $p |- ( ( A : RR --> RR /\ A. x e. RR ( A ` x ) = ( ( 2 x. x ) + 1 ) ) -> 3 e. ( A " { 1 , 2 } ) ) $=
    ( cr wf cv cfv c2 cmul co c1 caddc wceq wral wa cpr cima wcel c3 wss w3a simpl id syl 1re a1i 2re jca prssi csn cun cvv 1ex snidg elun1 df-pr eleqtrrd 3jca gfnfvima simpr wi fveq2d oveq2d oveq1d eqeq12d rspcv mpd eqid oveq12i 2cn mulridi eqtri 2p1e3 eqtr4i eqtrd eleq1d mpbid ) CCBDZAEZBFZGVRHIZJKIZLZACMZNZJBFZBJGOZPZQZRWGQWDVQWFCSZJWFQZTWHWDVQWIWJWDVQVQVQWCUAVQUBUCWDJCQZGCQZNWIWDWKWLWKWDUDUEZWLWDUFUEUGJGCUHUCWDJJUIZGUIZUJZWFWDJWNQZJWPQWDJUKQZWQWRWDULUEJUKUMUCJWNWOUNUCWFWPLWDJGUOUEUPUQCCJWFBURUCWDWERWGWDWEGJHIZJKIZRWDWCWEWTLZVQWCUSWDWKWCXAUTWMWBXAAJCVRJLZVSWEWAWTXBVRJBXBUBZVAXBVTWSJKXBVRJGHXCVBVCVDVEUCVFWTRLWDWTRRWTGJKIRWSGJJKWSWSGGGJJHGVGJVGZVHGVIVJVKXDVHVLVKRVGVMUEVNVOVP $.
$}
