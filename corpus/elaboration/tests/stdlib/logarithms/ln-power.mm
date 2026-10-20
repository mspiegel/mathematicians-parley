$( tests/stdlib/logarithms/ln-power, elaborated from tests/stdlib/logarithms.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.logarithms.ln-power $p |- ( ( ( A e. RR /\ B e. ZZ ) /\ 0 < A ) -> ( log ` ( A ^ B ) ) = ( B x. ( log ` A ) ) ) $=
    ( cr wcel cz wa cc0 clt wbr crp cexp co clog cfv cmul wceq simpl id syl simpr jca elrp sylibr relogexp ) ACDZBEDZFZGAHIZFZAJDZUFFABKLMNBAMNOLPUIUJUFUIUEUHFUJUIUEUHUIUGUEUGUHQZUGUEUEUEUFQUERSSUGUHTUAAUBUCUIUGUFUKUEUFTSUAABUDS $.
$}
