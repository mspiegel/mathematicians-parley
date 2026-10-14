$( tests/elaborator/order-chains/a-strict-link-then-a-bound, elaborated from tests/elaborator/order-chains.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.order-chains.a-strict-link-then-a-bound $p |- ( ( ( ( ( ( ( A e. RR /\ B e. RR ) /\ C e. RR ) /\ D e. RR ) /\ A < B ) /\ B <_ C ) /\ C < D ) -> A < D ) $=
    ( cr wcel wa clt wbr cle simpl id syl simpr ltletrd lttrd ) AEFZBEFZGZCEFZGZDEFZGZABHIZGZBCJIZGZCDHIZGZACDUIUGQUGUHKZUGUEQUEUFKZUEUCQUCUDKZUCUAQUAUBKZUASQSTKZSQQQRKZQLZMZMZMZMZMZMZUIUGTUJUGUETUKUEUCTULUCUATUMSTNZMZMZMZMZUIUGUBUJUGUEUBUKUEUCUBULUAUBNMMMUIABCVBUIUGRUJUGUERUKUEUCRULUCUARUMUASRUNQRNMMMMMVGUIUGUDUJUGUEUDUKUCUDNMMUIUGUFUJUEUFNMOUGUHNP $.
$}
