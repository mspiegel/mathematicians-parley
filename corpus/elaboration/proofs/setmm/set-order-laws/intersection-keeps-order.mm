$( proofs/setmm/set-order-laws/intersection-keeps-order, elaborated from proofs/setmm/set-order-laws.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A m $.
  $d B m $.
  $d C m $.
  proofs.setmm.set-order-laws.intersection-keeps-order $p |- ( ( ( ( A e. _V /\ B e. _V ) /\ C e. _V ) /\ A C_ B ) -> ( A i^i C ) C_ ( B i^i C ) ) $=
    ( cvv wcel wa wss cin vm cv wral simpl simpr syl wb elin a1i mpbid simpld jca ssel2 simprd mpbird ralrimiva dfss3 ) ADEZBDEZFZCDEZFZABGZFZACHZBCHZGZIJZUNEZIUMKZULUQIUMULUPUMEZFZUQUPBEZUPCEZFZUTVAVBUTUKUPAEZFVAUTUKVDUTULUKULUSLUJUKMNUTVDVBUTUSVDVBFZULUSMZUSVEOZUTUPACPZQZRZSTABUPUANUTVDVBVJUBTUQVCOUTUPBCPQUCUDUOUROULIUMUNUEQUC $.
$}
