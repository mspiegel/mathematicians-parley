$( tests/elaborator/reading-equations/an-equation-turned-in-a-transitivity, elaborated from tests/elaborator/reading-equations.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.reading-equations.an-equation-turned-in-a-transitivity $p |- ( ( ( ( ( A e. RR /\ B e. RR ) /\ C e. RR ) /\ B = A ) /\ B < C ) -> A < C ) $=
    ( cr wcel wa wceq clt wbr simpl simpr syl eqcomd eqbrtrd ) ADEZBDEZFZCDEZFZBAGZFZBCHIZFZABCHUCBAUCUATUAUBJSTKLMUAUBKN $.
$}
