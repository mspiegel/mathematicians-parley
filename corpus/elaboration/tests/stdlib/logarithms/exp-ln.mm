$( tests/stdlib/logarithms/exp-ln, elaborated from tests/stdlib/logarithms.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.logarithms.exp-ln $p |- ( ( A e. RR /\ 0 < A ) -> ( exp ` ( log ` A ) ) = A ) $=
    ( cr wcel cc0 clt wbr wa crp clog cfv ce wceq simpl id syl simpr jca elrp sylibr reeflog ) ABCZDAEFZGZAHCZAIJKJALUCUCUDUCUAUBUCUAUAUAUBMUANOUAUBPQARSATO $.
$}
