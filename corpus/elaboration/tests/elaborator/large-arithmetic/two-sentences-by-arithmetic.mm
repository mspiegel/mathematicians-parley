$( tests/elaborator/large-arithmetic/two-sentences-by-arithmetic, elaborated from tests/elaborator/large-arithmetic.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.large-arithmetic.two-sentences-by-arithmetic $p |- ( ( 2 + 2 ) = 4 /\ ( 3 x. 3 ) = 9 ) $=
    ( c2 caddc co c4 wceq c3 cmul c9 wa wtru eqid oveq12i 2p2e4 eqtri eqtr4i a1i 3t3e9 jca mptru ) AABCZDEZFFGCZHEZIJUAUCUAJTDDTTDAAAABAKZUDLMNDKOPUCJUBHHUBUBHFFFFGFKZUELQNHKOPRS $.
$}
