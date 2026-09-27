$( tests/stdlib/reasoning/or-right, elaborated from tests/stdlib/reasoning.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  orright $p |- ( ( A e. RR /\ A = 1 ) -> ( A = 0 \/ A = 1 ) ) $=
    ( cr wcel c1 wceq wa cc0 wo simpr olc syl ) ABCZADEZFMAGEZMHLMIMNJK $.
$}
