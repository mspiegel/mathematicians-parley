$( tests/stdlib/numbers/power-at-least-one, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.power-at-least-one $p |- ( ( ( A e. RR /\ B e. NN0 ) /\ 1 <_ A ) -> 1 <_ ( A ^ B ) ) $=
    ( cr wcel cn0 wa c1 cle wbr w3a cexp co simpl id syl simpr 3jca expge1 ) ACDZBEDZFZGAHIZFZSTUBJGABKLHIUCSTUBUCUASUAUBMZUASSSTMSNOOUCUATUDSTPOUAUBPQABRO $.
$}
