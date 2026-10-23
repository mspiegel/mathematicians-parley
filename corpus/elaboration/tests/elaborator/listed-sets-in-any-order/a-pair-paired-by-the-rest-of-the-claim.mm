$( tests/elaborator/listed-sets-in-any-order/a-pair-paired-by-the-rest-of-the-claim, elaborated from tests/elaborator/listed-sets-in-any-order.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.listed-sets-in-any-order.a-pair-paired-by-the-rest-of-the-claim $p |- ( ( ( A e. _V /\ B e. _V ) /\ C e. _V ) -> ( A e. { B , C } <-> ( A = C \/ A = B ) ) ) $=
    ( cvv wcel wa cpr wceq wo wb simpl id syl elprg prcom a1i eleq2d bibi1d mpbid ) ADEZBDEZFZCDEZFZACBGZEZACHZABHZIZJZABCGZEZUIJUDTUJUDUBTUBUCKUBTTTUAKTLMMACBDNMUDUFULUIUDUEUKAUEUKHUDCBOPQRS $.
$}
