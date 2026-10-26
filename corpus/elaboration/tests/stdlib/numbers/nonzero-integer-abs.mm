$( tests/stdlib/numbers/nonzero-integer-abs, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.numbers.nonzero-integer-abs $p |- ( ( A e. ZZ /\ -. A = 0 ) -> 1 <_ ( abs ` A ) ) $=
    ( cz wcel cc0 wceq wn wa wne c1 cabs cfv cle wbr simpl id syl simpr neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid jca gzabsge1 ) ABCZADEZFZGZUIADHZGIAJKLMULUIUMULUIUIUIUKNUIOPULDAEZFZUMULADUIUKQRULUMUOULUMUKUOUMUKSULADTUAULUJUNULUNUJUNUJSULDAUBUAUCUDUEUCUFUGAUHP $.
$}
