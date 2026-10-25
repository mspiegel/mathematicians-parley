$( tests/elaborator/reading-equations/an-equation-turned-joined, elaborated from tests/elaborator/reading-equations.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.reading-equations.an-equation-turned-joined $p |- ( ( ( A e. RR /\ B e. RR ) /\ B = A ) -> A = B ) $=
    ( cr wcel wa wceq simpr wb eqcom a1i mpbid ) ACDZBCDZEZBAFZEZOABFZNOGOQHPBAIJK $.
$}
