$( tests/elaborator/transitivity/a-chain-through-an-equation, elaborated from tests/elaborator/transitivity.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.transitivity.a-chain-through-an-equation $p |- ( ( ( ( ( A e. RR /\ B e. RR ) /\ C e. RR ) /\ B = A ) /\ B <_ C ) -> A <_ C ) $=
    ( cr wcel wa wceq cle wbr simpl simpr syl eqcomd eqbrtrd ) ADEZBDEZFZCDEZFZBAGZFZBCHIZFZABCHUCBAUCUATUAUBJSTKLMUAUBKN $.
$}
