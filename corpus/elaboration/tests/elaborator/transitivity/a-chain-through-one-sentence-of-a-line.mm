$( tests/elaborator/transitivity/a-chain-through-one-sentence-of-a-line, elaborated from tests/elaborator/transitivity.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.transitivity.a-chain-through-one-sentence-of-a-line $p |- ( ( ( ( ( A e. RR /\ B e. RR ) /\ C e. RR ) /\ ( 0 < A /\ A <_ B ) ) /\ B < C ) -> A < C ) $=
    ( cr wcel wa cc0 clt wbr cle simpl id syl simpr lelttrd ) ADEZBDEZFZCDEZFZGAHIZABJIZFZFZBCHIZFZABCUFUDPUDUEKZUDTPTUCKZTRPRSKZRPPPQKPLMMMMUFUDQUGUDTQUHTRQUIPQNMMMUFUDSUGUDTSUHRSNMMUFUCUBUFUDUCUGTUCNMUAUBNMUDUENO $.
$}
