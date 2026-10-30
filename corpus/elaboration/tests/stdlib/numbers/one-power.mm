$( tests/stdlib/numbers/one-power, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.one-power $p |- ( A e. ZZ -> ( 1 ^ A ) = 1 ) $=
    ( 1exp ) AB $.
$}
