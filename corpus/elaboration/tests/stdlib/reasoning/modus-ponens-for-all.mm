$( tests/stdlib/reasoning/modus-ponens-for-all, elaborated from tests/stdlib/reasoning.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A x $.
  tests.stdlib.reasoning.modus-ponens-for-all $p |- ( ( ( A e. NN /\ ( A <_ 3 -> A. x e. RR ( -. x = 0 -> 0 < ( x ^ 2 ) ) ) ) /\ A <_ 3 ) -> A. x e. RR ( -. x = 0 -> 0 < ( x ^ 2 ) ) ) $=
    ( cn wcel c3 cle wbr cv cc0 wceq wn c2 cexp co clt wi cr wral wa simpr simpl syl mpd ) BCDZBEFGZAHZIJZKZIUFLMNZOGZPZAQRZPZSZUESZUEULUNUETUOUNUMUNUEUAUDUMTUBUC $.
$}
