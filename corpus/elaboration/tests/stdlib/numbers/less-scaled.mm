$( tests/stdlib/numbers/less-scaled, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.less-scaled $p |- ( ( ( ( A e. RR /\ B e. RR ) /\ C e. RR ) /\ 0 < C ) -> ( A < B <-> ( C x. A ) < ( C x. B ) ) ) $=
    ( cr wcel wa cc0 clt wbr w3a cmul co wb simpl id syl simpr jca 3jca ltmul2 ) ADEZBDEZFZCDEZFZGCHIZFZUAUBUDUFFZJABHICAKLCBKLHIMUGUAUBUHUGUEUAUEUFNZUEUCUAUCUDNZUCUAUAUAUBNUAOPPPUGUEUBUIUEUCUBUJUAUBQPPUGUDUFUGUEUDUIUCUDQPUEUFQRSABCTP $.
$}
