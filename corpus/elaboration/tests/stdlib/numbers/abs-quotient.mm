$( tests/stdlib/numbers/abs-quotient, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.abs-quotient $p |- ( ( ( A e. RR /\ B e. RR ) /\ -. B = 0 ) -> ( abs ` ( A / B ) ) = ( ( abs ` A ) / ( abs ` B ) ) ) $=
    ( cr wcel wa cc0 wceq wn cc wne w3a cdiv co cabs cfv simpl id syl recn simpr neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid 3jca absdiv ) ACDZBCDZEZBFGZHZEZAIDZBIDZBFJZKABLMNOANOBNOLMGUQURUSUTUQULURUQUNULUNUPPZUNULULULUMPULQRRASRUQUMUSUQUNUMVAULUMTRBSRUQFBGZHZUTUQBFUNUPTUAUQUTVCUQUTUPVCUTUPUBUQBFUCUDUQUOVBUQVBUOVBUOUBUQFBUEUDUFUGUHUFUIUJABUKR $.
$}
