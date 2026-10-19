$( tests/stdlib/numbers/exponent-negative, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.exponent-negative $p |- ( ( ( A e. RR /\ -. A = 0 ) /\ B e. ZZ ) -> ( A ^ -u B ) = ( 1 / ( A ^ B ) ) ) $=
    ( cr wcel cc0 wceq wn wa cz cc wne w3a cneg cexp co c1 cdiv simpl id syl recn simpr neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid 3jca expnegz ) ACDZAEFZGZHZBIDZHZAJDZAEKZURLABMNOPABNOQOFUSUTVAURUSUNUTUSUQUNUQURRZUQUNUNUNUPRUNSTTAUATUSEAFZGZVAUSAEUSUQUPVBUNUPUBTUCUSVAVDUSVAUPVDVAUPUDUSAEUEUFUSUOVCUSVCUOVCUOUDUSEAUGUFUHUIUJUHUKUQURUBULABUMT $.
$}
