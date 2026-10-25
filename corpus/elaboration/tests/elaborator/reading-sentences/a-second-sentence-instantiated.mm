$( tests/elaborator/reading-sentences/a-second-sentence-instantiated, elaborated from tests/elaborator/reading-sentences.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A x $.
  $d B x $.
  tests.elaborator.reading-sentences.a-second-sentence-instantiated $p |- ( ( ( A e. RR /\ B e. RR ) /\ ( A = 1 /\ A. x e. RR ( x x. 0 ) = 0 ) ) -> ( B x. 0 ) = 0 ) $=
    ( cr wcel wa c1 wceq cv cc0 cmul co wral simpr syl wi simpl id oveq1d eqeq1d rspcv mpd ) BDEZCDEZFZBGHZAIZJKLZJHZADMZFZFZUJCJKLZJHZULUKUJUEUKNUFUJNOULUDUJUNPULUEUDUEUKQUCUDNOUIUNACDUGCHZUHUMJUOUGCJKUORSTUAOUB $.
$}
