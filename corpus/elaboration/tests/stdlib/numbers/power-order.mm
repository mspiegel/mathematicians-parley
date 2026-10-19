$( tests/stdlib/numbers/power-order, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.power-order $p |- ( ( ( ( A e. RR /\ B e. ZZ ) /\ C e. ZZ ) /\ 1 < A ) -> ( B < C <-> ( A ^ B ) < ( A ^ C ) ) ) $=
    ( cr wcel cz wa c1 clt wbr w3a cexp co wb simpl id syl simpr 3jca jca ltexp2 ) ADEZBFEZGZCFEZGZHAIJZGZUBUCUEKZUGGBCIJABLMACLMIJNUHUIUGUHUBUCUEUHUFUBUFUGOZUFUDUBUDUEOZUDUBUBUBUCOUBPQQQUHUFUCUJUFUDUCUKUBUCRQQUHUFUEUJUDUERQSUFUGRTABCUAQ $.
$}
