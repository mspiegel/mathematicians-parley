$( tests/stdlib/numbers/power-nat0, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.power-nat0 $p |- ( ( A e. NN0 /\ B e. NN0 ) -> ( A ^ ( B + 1 ) ) e. NN0 ) $=
    ( cn0 wcel wa c1 caddc co cexp simpl id syl simpr 1nn0 a1i nn0addcld jca nn0expcl ) ACDZBCDZEZSBFGHZCDZEAUBIHCDUASUCUASSSTJSKLUABFSTMFCDUANOPQAUBRL $.
$}
