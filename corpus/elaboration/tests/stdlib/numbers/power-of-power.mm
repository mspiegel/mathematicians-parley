$( tests/stdlib/numbers/power-of-power, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.power-of-power $p |- ( ( ( A e. CC /\ B e. NN0 ) /\ C e. NN0 ) -> ( A ^ ( B x. C ) ) = ( ( A ^ B ) ^ C ) ) $=
    ( cc wcel cn0 wa w3a cmul co cexp wceq simpl id syl simpr 3jca expmul ) ADEZBFEZGZCFEZGZSTUBHABCIJKJABKJCKJLUCSTUBUCUASUAUBMZUASSSTMSNOOUCUATUDSTPOUAUBPQABCRO $.
$}
