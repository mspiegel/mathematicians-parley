$( tests/stdlib/numbers/minus-one-even-power, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.minus-one-even-power $p |- ( A e. ZZ -> ( -u 1 ^ ( 2 x. A ) ) = 1 ) $=
    ( m1expeven ) AB $.
$}
