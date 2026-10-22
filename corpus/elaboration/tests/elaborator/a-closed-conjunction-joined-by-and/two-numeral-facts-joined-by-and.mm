$( tests/elaborator/a-closed-conjunction-joined-by-and/two-numeral-facts-joined-by-and, elaborated from tests/elaborator/a-closed-conjunction-joined-by-and.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.a-closed-conjunction-joined-by-and.two-numeral-facts-joined-by-and $p |- ( ( 2 x. 3 ) = 6 /\ 1 < 2 ) $=
    ( c2 c3 cmul co c6 wceq c1 clt wbr wa wtru eqid oveq12i 2t3e6 eqtri eqtr4i a1i 1lt2 jca mptru ) ABCDZEFZGAHIZJKUBUCUBKUAEEUAUAEAABBCALBLMNOELPQUCKRQST $.
$}
