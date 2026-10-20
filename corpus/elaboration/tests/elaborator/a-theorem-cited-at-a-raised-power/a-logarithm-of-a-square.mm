$( tests/elaborator/a-theorem-cited-at-a-raised-power/a-logarithm-of-a-square, elaborated from tests/elaborator/a-theorem-cited-at-a-raised-power.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.a-theorem-cited-at-a-raised-power.a-logarithm-of-a-square $p |- ( ( A e. RR /\ 0 < A ) -> ( log ` ( A ^ 2 ) ) = ( 2 x. ( log ` A ) ) ) $=
    ( cr wcel cc0 clt wbr wa crp c2 cz cexp co clog cfv cmul wceq simpl id syl simpr jca elrp sylibr 2z a1i relogexp ) ABCZDAEFZGZAHCZIJCZGAIKLMNIAMNOLPUIUJUKUIUIUJUIUGUHUIUGUGUGUHQUGRSUGUHTUAAUBUCUKUIUDUEUAAIUFS $.
$}
