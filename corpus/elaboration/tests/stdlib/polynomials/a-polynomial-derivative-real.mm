$( tests/stdlib/polynomials/a-polynomial-derivative-real, elaborated from tests/stdlib/polynomials.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d k m x $.
  $d A k m x $.
  $d B k m x $.
  tests.stdlib.polynomials.a-polynomial-derivative-real $p |- ( ( ( ( A : CC --> CC /\ A e. ( Poly ` ZZ ) ) /\ B : RR --> RR ) /\ A. x e. RR ( B ` x ) = ( A ` x ) ) -> ( ( ( ( B |` RR ) e. ( RR -cn-> RR ) /\ RR C_ dom ( RR _D B ) ) /\ ( RR _D B ) : RR --> RR ) /\ ( ( RR _D B ) |` RR ) e. ( RR -cn-> RR ) ) ) $=
    ( cc wf cz cply cfv wcel wa cr cv wceq wral cres ccncf co cdv cdm wss vm simpl simpr syl wb vk id fveq2d eqeq12d cbvralvw bitri a1i mpbid gplyrecn gplyredv jca gplyredvf gplyredvcn ) DDBEZBFGHZIZJZKKCEZJZALZCHZVEBHZMZAKNZJZCKOZKKPQZIZKKCRQZSZTZJZKKVNEZJVNKOVLIVJVQVRVJVMVPVJUABCVJVDVAVDVIUBZVDVBVAVBVCUBZUSVAUCZUDZUDZVJVDVCVSVBVCUCZUDZVJVIUALZCHZWFBHZMZUAKNZVDVIUCZVIWJUEZVJVIUFLZCHZWMBHZMZUFKNZWJVHWPAUFKVEWMMZVFWNVGWOWRVEWMCWRUGZUHZWRVEWMBWSUHZUIZUJZWPWIUFUAKWMWFMZWNWGWOWHXDWMWFCXDUGZUHZXDWMWFBXEUHZUIZUJZUKZULZUMZUNVJUABCWCWEXLUOUPVJUABCWCWEXLUQUPVJUABCWCWEXLURUP $.
$}
