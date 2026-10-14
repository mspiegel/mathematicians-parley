$( tests/stdlib/numbers/quotient-positive, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.quotient-positive $p |- ( ( ( ( A e. RR /\ B e. RR ) /\ 0 < A ) /\ 0 < B ) -> 0 < ( A / B ) ) $=
    ( cr wcel wa cc0 clt wbr cdiv co simpl id syl simpr jca divgt0 ) ACDZBCDZEZFAGHZEZFBGHZEZQTEZRUBEZEFABIJGHUCUDUEUCQTUCUAQUAUBKZUASQSTKZSQQQRKQLMMMUCUATUFSTNMOUCRUBUCUARUFUASRUGQRNMMUAUBNOOABPM $.
$}
