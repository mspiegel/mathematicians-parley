$( tests/stdlib/counting/binomial-two, elaborated from tests/stdlib/counting.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.counting.binomial-two $p |- ( A e. NN0 -> ( A _C 2 ) = ( ( A x. ( A - 1 ) ) / 2 ) ) $=
    ( cn0 wcel c2 cbc co c1 cmin cmul cdiv wceq id bcn2 syl ) ABCZOADEFAAGHFIFDJFKOLAMN $.
$}
