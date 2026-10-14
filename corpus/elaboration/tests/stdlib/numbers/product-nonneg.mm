$( tests/stdlib/numbers/product-nonneg, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.product-nonneg $p |- ( ( ( ( A e. RR /\ B e. RR ) /\ 0 <_ A ) /\ 0 <_ B ) -> 0 <_ ( A x. B ) ) $=
    ( cr wcel wa cc0 cle wbr cmul co simpl id syl simpr jca mulge0 ) ACDZBCDZEZFAGHZEZFBGHZEZQTEZRUBEZEFABIJGHUCUDUEUCQTUCUAQUAUBKZUASQSTKZSQQQRKQLMMMUCUATUFSTNMOUCRUBUCUARUFUASRUGQRNMMUAUBNOOABPM $.
$}
