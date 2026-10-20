$( tests/stdlib/numbers/power-of-power-integer, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.power-of-power-integer $p |- ( ( ( ( A e. CC /\ -. A = 0 ) /\ B e. ZZ ) /\ C e. ZZ ) -> ( A ^ ( B x. C ) ) = ( ( A ^ B ) ^ C ) ) $=
    ( cc wcel cc0 wceq wn wa cz wne cmul co cexp simpl id syl simpr neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid jca expmulz ) ADEZAFGZHZIZBJEZIZCJEZIZUJAFKZIZUNUPIZIABCLMNMABNMCNMGUQUSUTUQUJURUQUOUJUOUPOZUOUMUJUMUNOZUMUJUJUJULOUJPQQQUQFAGZHZURUQAFUQUOULVAUOUMULVBUJULRQQSUQURVDUQURULVDURULTUQAFUAUBUQUKVCUQVCUKVCUKTUQFAUCUBUDUEUFUDUGUHUQUNUPUQUOUNVAUMUNRQUOUPRUHUHABCUIQ $.
$}
