$( tests/stdlib/divisibility/prime-divides-power, elaborated from tests/stdlib/divisibility.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.divisibility.prime-divides-power $p |- ( ( ( ( A e. NN /\ A e. Prime ) /\ B e. ZZ ) /\ C e. NN ) -> ( A || ( B ^ C ) <-> A || B ) ) $=
    ( cn wcel cprime wa cz w3a cexp co cdvds wbr wb simpl simpr syl 3jca prmdvdsexp ) ADEZAFEZGZBHEZGZCDEZGZUAUCUEIABCJKLMABLMNUFUAUCUEUFUDUAUDUEOZUDUBUAUBUCOTUAPQQUFUDUCUGUBUCPQUDUEPRBACSQ $.
$}
