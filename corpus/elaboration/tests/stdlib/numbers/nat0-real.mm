$( tests/stdlib/numbers/nat0-real, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.nat0-real $p |- ( A e. NN0 -> A e. RR ) $=
    ( cn0 wcel cr id nn0re syl ) ABCZHADCHEAFG $.
$}
