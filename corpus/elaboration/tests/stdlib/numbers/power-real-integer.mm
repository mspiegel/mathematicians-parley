$( tests/stdlib/numbers/power-real-integer, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.power-real-integer $p |- ( ( ( A e. RR /\ -. A = 0 ) /\ B e. ZZ ) -> ( A ^ ( B - 1 ) ) e. RR ) $=
    ( cr wcel cc0 wceq wn wa cz wne c1 cmin co w3a cexp simpl id syl simpr neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid 1z zsubcld 3jca reexpclz ) ACDZAEFZGZHZBIDZHZUMAEJZBKLMZIDZNAUTOMCDURUMUSVAURUPUMUPUQPZUPUMUMUMUOPUMQRRUREAFZGZUSURAEURUPUOVBUMUOSRTURUSVDURUSUOVDUSUOUAURAEUBUCURUNVCURVCUNVCUNUAUREAUDUCUEUFUGUEUHURBKUPUQSKIDURUIUCUJUKAUTULR $.
$}
