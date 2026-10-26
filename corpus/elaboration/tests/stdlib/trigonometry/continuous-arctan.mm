$( tests/stdlib/trigonometry/continuous-arctan, elaborated from tests/stdlib/trigonometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d k m y $.
  $d A k m y $.
  $d B k m y $.
  tests.stdlib.trigonometry.continuous-arctan $p |- ( ( ( A e. ~P RR /\ B : A --> RR ) /\ A. y e. A ( B ` y ) = ( arctan ` y ) ) -> ( B |` A ) e. ( A -cn-> RR ) ) $=
    ( cr cpw wcel wf wa cv cfv catan wceq wral vm wss simpl id syl elpwi simpr wb vk fveq2d eqeq12d cbvralvw bitri a1i mpbid gcncfatanres ) BDEZFZBDCGZHZAIZCJZUNKJZLZABMZHZNBCUSUKBDOUSUMUKUMURPZUMUKUKUKULPUKQRRBDSRUSUMULUTUKULTRUSURNIZCJZVAKJZLZNBMZUMURTURVEUAUSURUBIZCJZVFKJZLZUBBMVEUQVIAUBBUNVFLZUOVGUPVHVJUNVFCVJQZUCVJUNVFKVKUCUDUEVIVDUBNBVFVALZVGVBVHVCVLVFVACVLQZUCVLVFVAKVMUCUDUEUFUGUHUI $.
$}
