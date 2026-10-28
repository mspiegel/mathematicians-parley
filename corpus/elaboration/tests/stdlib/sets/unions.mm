$( tests/stdlib/sets/unions, elaborated from tests/stdlib/sets.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A m $.
  tests.stdlib.sets.unions $p |- ( ( A e. _V /\ A e. _V ) -> U_ m e. A m e. _V ) $=
    ( cvv wcel wa cv ciun simpr giunex syl ) ACDZKEKBABFGCDKKHBACIJ $.
$}
