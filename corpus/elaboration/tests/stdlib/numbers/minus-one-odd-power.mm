$( tests/stdlib/numbers/minus-one-odd-power, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.minus-one-odd-power $p |- ( ( A e. ZZ /\ ( A e. ZZ /\ -. 2 || A ) ) -> ( -u 1 ^ A ) = -u 1 ) $=
    ( cz wcel c2 cdvds wbr wn wa c1 cneg cexp co wceq simpr m1expo syl ) ABCZQDAEFZGZHZHTIJZAKLUAMQTNAOP $.
$}
