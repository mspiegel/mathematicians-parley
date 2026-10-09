$( tests/stdlib/numbers/below-successor, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.below-successor $p |- ( A e. RR -> A < ( A + 1 ) ) $=
    ( cr wcel c1 caddc co clt wbr id ltp1 syl ) ABCZLAADEFGHLIAJK $.
$}
