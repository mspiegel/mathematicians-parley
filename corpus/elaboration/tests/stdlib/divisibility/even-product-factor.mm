$( tests/stdlib/divisibility/even-product-factor, elaborated from tests/stdlib/divisibility.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.divisibility.even-product-factor $p |- ( ( A e. ZZ /\ B e. ZZ ) -> ( 2 || ( A x. B ) <-> ( 2 || A \/ 2 || B ) ) ) $=
    ( cz wcel wa c2 cprime w3a cmul co cdvds wbr wo wb 2prm a1i simpl id syl simpr 3jca euclemma ) ACDZBCDZEZFGDZUCUDHFABIJKLFAKLFBKLMNUEUFUCUDUFUEOPUEUCUCUCUDQUCRSUCUDTUAFABUBS $.
$}
