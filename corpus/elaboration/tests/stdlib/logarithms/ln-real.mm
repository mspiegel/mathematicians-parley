$( tests/stdlib/logarithms/ln-real, elaborated from tests/stdlib/logarithms.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.logarithms.ln-real $p |- ( ( A e. RR /\ 0 < A ) -> ( log ` A ) e. RR ) $=
    ( cr wcel cc0 clt wbr wa crp clog cfv simpl id syl simpr jca elrp sylibr relogcl ) ABCZDAEFZGZAHCZAIJBCUAUAUBUASTUASSSTKSLMSTNOAPQARM $.
$}
