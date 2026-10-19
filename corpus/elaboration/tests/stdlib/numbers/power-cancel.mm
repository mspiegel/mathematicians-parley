$( tests/stdlib/numbers/power-cancel, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.power-cancel $p |- ( ( ( ( A e. RR /\ B e. ZZ ) /\ C e. ZZ ) /\ 1 < A ) -> ( ( A ^ B ) = ( A ^ C ) <-> B = C ) ) $=
    ( cr wcel cz wa c1 clt wbr w3a cexp co wceq wb simpl id syl simpr 3jca jca expcan ) ADEZBFEZGZCFEZGZHAIJZGZUCUDUFKZUHGABLMACLMNBCNOUIUJUHUIUCUDUFUIUGUCUGUHPZUGUEUCUEUFPZUEUCUCUCUDPUCQRRRUIUGUDUKUGUEUDULUCUDSRRUIUGUFUKUEUFSRTUGUHSUAABCUBR $.
$}
