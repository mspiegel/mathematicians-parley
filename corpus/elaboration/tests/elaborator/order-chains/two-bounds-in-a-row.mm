$( tests/elaborator/order-chains/two-bounds-in-a-row, elaborated from tests/elaborator/order-chains.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.order-chains.two-bounds-in-a-row $p |- ( ( ( ( ( A e. RR /\ B e. RR ) /\ C e. RR ) /\ A <_ B ) /\ B <_ C ) -> A <_ C ) $=
    ( cr wcel wa cle wbr cxr simpl simpr syl lerelxr brel simpld simprd xrletrd ) ADEZBDEZFZCDEZFZABGHZFZBCGHZFZABCUFAIEZBIEZUFUCUGUHFZUFUDUCUDUEJZUBUCKZLZABIIGMNZLZOUFUGUHUNPUFUHCIEZUFUEUHUOFUDUEKZBCIIGMNLPULUPQ $.
$}
