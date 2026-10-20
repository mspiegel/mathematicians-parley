$( tests/stdlib/numbers/power-of-product, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.power-of-product $p |- ( ( ( A e. CC /\ B e. CC ) /\ C e. NN0 ) -> ( ( A x. B ) ^ C ) = ( ( A ^ C ) x. ( B ^ C ) ) ) $=
    ( cc wcel wa cn0 w3a cmul co cexp wceq simpl id syl simpr 3jca mulexp ) ADEZBDEZFZCGEZFZSTUBHABIJCKJACKJBCKJIJLUCSTUBUCUASUAUBMZUASSSTMSNOOUCUATUDSTPOUAUBPQABCRO $.
$}
