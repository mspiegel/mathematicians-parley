$( tests/elaborator/reading-equations/an-equation-turned-substituted, elaborated from tests/elaborator/reading-equations.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.reading-equations.an-equation-turned-substituted $p |- ( ( A e. RR /\ A = 2 ) -> ( 2 + 1 ) = ( A + 1 ) ) $=
    ( cr wcel c2 wceq wa c1 caddc simpr eqcomd oveq1d ) ABCZADEZFZDAGHNADLMIJK $.
$}
