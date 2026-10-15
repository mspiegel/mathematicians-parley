$( tests/stdlib/numbers/abs-positive, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.abs-positive $p |- ( ( A e. RR /\ -. A = 0 ) -> 0 < ( abs ` A ) ) $=
    ( cr wcel cc0 wceq wn wa wne cabs cfv clt wbr simpr neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid cc simpl id syl recn absgt0 ) ABCZADEZFZGZADHZDAIJZKLZULDAEZFZUMULADUIUKMNULUMUQULUMUKUQUMUKOULADPQULUJUPULUPUJUPUJOULDARQSTUASUBULAUCCZUMUOOULUIURULUIUIUIUKUDUIUEUFAUGUFAUHUFUB $.
$}
