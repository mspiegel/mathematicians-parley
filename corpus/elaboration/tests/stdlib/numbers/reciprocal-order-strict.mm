$( tests/stdlib/numbers/reciprocal-order-strict, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.reciprocal-order-strict $p |- ( ( ( ( A e. RR /\ 0 < A ) /\ B e. RR ) /\ 0 < B ) -> ( A < B <-> ( 1 / B ) < ( 1 / A ) ) ) $=
    ( cr wcel cc0 clt wbr wa c1 cdiv co wb simpl id syl simpr jca ltrec ) ACDZEAFGZHZBCDZHZEBFGZHZUAUBUDHZHABFGIBJKIAJKFGLUEUAUFUESTUEUCSUCUDMZUCUASUAUBMZUASSSTMSNOOOUEUCTUGUCUATUHSTPOOQUEUBUDUEUCUBUGUAUBPOUCUDPQQABRO $.
$}
