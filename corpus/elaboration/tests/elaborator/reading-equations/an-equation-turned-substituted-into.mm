$( tests/elaborator/reading-equations/an-equation-turned-substituted-into, elaborated from tests/elaborator/reading-equations.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.reading-equations.an-equation-turned-substituted-into $p |- ( ( ( ( A e. RR /\ B e. RR ) /\ ( A + 1 ) = B ) /\ A = 2 ) -> B = ( 2 + 1 ) ) $=
    ( cr wcel wa c1 caddc co wceq c2 simpl simpr syl eqcomd oveq1d eqeq2d mpbid ) ACDZBCDZEZAFGHZBIZEZAJIZEZBUAIBJFGHZIUEUABUEUCUBUCUDKTUBLMNUEUAUFBUEAJFGUCUDLOPQ $.
$}
