$( tests/elaborator/a-sequence-given-as-a-map/a-late-bound-of-a-letter, elaborated from tests/elaborator/a-sequence-given-as-a-map.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/calculus/limit-at-most.mm $]

${
  $d i j k m n $.
  $d A i j k m n $.
  $d B i j k m n $.
  tests.elaborator.a-sequence-given-as-a-map.a-late-bound-of-a-letter $p |- ( ( ( ( A : NN --> RR /\ B e. RR ) /\ ( n e. NN |-> ( A ` n ) ) ~~> B ) /\ A. i e. NN ( 1 <_ i -> ( A ` i ) <_ 1 ) ) -> B <_ 1 ) $=
    ( cn cr wf wcel wa cv cfv cmpt cli wbr c1 cle wi wral vk vm cdiv co wceq wex cvv nnex a1i mptexg syl elisset simpl id simpr jca 1re 1nn wb vj breq2d fveq2d breq1d imbi12d cbvralvw bitri mpbid stdlib.calculus.limit-at-most ex exlimdv mpd ) EFAGZBFHZIZDEDJZAKZLZBMNZIZOCJZPNZVRAKZOPNZQZCERZIZSJZTEOTJZUAUBZLZUCZSUDZBOPNZWDWHUEHZWJWDEUEHZWLWMWDUFUGTEWGUEUHUISWHUEUJUIWDWIWKSWDWIWKWDWIIZVQOFHZIZOEHZIZOVMPNZVNOPNZQZDERZIWKWNWRXBWNWPWQWNVQWOWNVLVPWNVJVKWNWDVJWDWIUKZWDVQVJVQWCUKZVQVLVJVLVPUKZVLVJVJVJVKUKVJULUIUIUIUIWNWDVKXCWDVQVKXDVQVLVKXEVJVKUMUIUIUIUNWNWDVPXCWDVQVPXDVLVPUMUIUIUNWOWNUOUGUNWQWNUPUGUNWNWCXBWNWDWCXCVQWCUMUIWCXBUQWNWCOURJZPNZXFAKZOPNZQZURERXBWBXJCUREVRXFUCZVSXGWAXIXKVRXFOPXKULZUSXKVTXHOPXKVRXFAXLUTVAVBVCXJXAURDEXFVMUCZXGWSXIWTXMXFVMOPXMULZUSXMXHVNOPXMXFVMAXNUTVAVBVCVDUGVEUNABOODVFUIVGVHVI $.
$}
