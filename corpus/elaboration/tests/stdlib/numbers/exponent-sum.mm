$( tests/stdlib/numbers/exponent-sum, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.exponent-sum $p |- ( ( ( A e. RR /\ B e. NN0 ) /\ C e. NN0 ) -> ( A ^ ( B + C ) ) = ( ( A ^ B ) x. ( A ^ C ) ) ) $=
    ( cr wcel cn0 wa cc w3a caddc co cexp cmul wceq simpl id syl recn simpr 3jca expadd ) ADEZBFEZGZCFEZGZAHEZUCUEIABCJKLKABLKACLKMKNUFUGUCUEUFUBUGUFUDUBUDUEOZUDUBUBUBUCOUBPQQARQUFUDUCUHUBUCSQUDUESTABCUAQ $.
$}
