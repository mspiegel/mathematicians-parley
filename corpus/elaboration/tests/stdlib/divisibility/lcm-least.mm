$( tests/stdlib/divisibility/lcm-least, elaborated from tests/stdlib/divisibility.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A k $.
  $d B k $.
  tests.stdlib.divisibility.lcm-least $p |- ( ( A e. ZZ /\ B e. ZZ ) -> A. k e. ZZ ( ( A || k /\ B || k ) -> ( A lcm B ) || k ) ) $=
    ( cz wcel wa cv cdvds wbr clcm co wi w3a simpr simpl id syl 3jca lcmdvds ralrimiva ) ADEZBDEZFZACGZHIZBUDHIZFZABJKZUDHIZLZCDUCUDDEZFZUKUAUBMUJULUKUAUBUCUKNULUCUAUCUKOZUCUAUAUAUBOUAPQQULUCUBUMUAUBNQRUDABSQT $.
$}
