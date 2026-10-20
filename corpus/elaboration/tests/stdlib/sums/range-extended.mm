$( tests/stdlib/sums/range-extended, elaborated from tests/stdlib/sums.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.sums.range-extended $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ C e. ( A ... B ) ) -> C e. ( A ... ( B + 1 ) ) ) $=
    ( cz wcel wa cfz co c1 caddc simpr fzelp1 syl ) ADEZBDEZFZCABGHZEZFRCABIJHGHEPRKCABLM $.
$}
