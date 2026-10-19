$( tests/stdlib/logarithms/ln-product, elaborated from tests/stdlib/logarithms.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.logarithms.ln-product $p |- ( ( ( ( A e. RR /\ B e. RR ) /\ 0 < A ) /\ 0 < B ) -> ( log ` ( A x. B ) ) = ( ( log ` A ) + ( log ` B ) ) ) $=
    ( cr wcel wa cc0 clt wbr crp cmul co clog cfv caddc wceq simpl id syl simpr elrpd jca relogmul ) ACDZBCDZEZFAGHZEZFBGHZEZAIDZBIDZEABJKLMALMBLMNKOUIUJUKUIAUIUGUCUGUHPZUGUEUCUEUFPZUEUCUCUCUDPUCQRRRUIUGUFULUEUFSRTUIBUIUGUDULUGUEUDUMUCUDSRRUGUHSTUAABUBR $.
$}
