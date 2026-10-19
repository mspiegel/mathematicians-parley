$( tests/stdlib/divisibility/prime-divides-product, elaborated from tests/stdlib/divisibility.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.divisibility.prime-divides-product $p |- ( ( ( ( A e. NN /\ A e. Prime ) /\ B e. ZZ ) /\ C e. ZZ ) -> ( A || ( B x. C ) <-> ( A || B \/ A || C ) ) ) $=
    ( cn wcel cprime wa cz w3a cmul co cdvds wbr wo wb simpl simpr syl 3jca euclemma ) ADEZAFEZGZBHEZGZCHEZGZUBUDUFIABCJKLMABLMACLMNOUGUBUDUFUGUEUBUEUFPZUEUCUBUCUDPUAUBQRRUGUEUDUHUCUDQRUEUFQSABCTR $.
$}
