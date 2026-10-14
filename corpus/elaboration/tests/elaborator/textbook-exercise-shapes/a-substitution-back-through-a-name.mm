$( tests/elaborator/textbook-exercise-shapes/a-substitution-back-through-a-name, elaborated from tests/elaborator/textbook-exercise-shapes.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A m $.
  $d B m $.
  $d C m $.
  tests.elaborator.textbook-exercise-shapes.a-substitution-back-through-a-name $p |- ( ( ( ( A e. RR /\ B e. RR ) /\ C e. RR ) /\ ( abs ` ( B - ( A / 2 ) ) ) < C ) -> ( abs ` ( B - ( A / 2 ) ) ) < C ) $=
    ( cr wcel wa c2 cdiv co cmin cabs cfv clt wbr vm cv wceq wex cvv ovex a1i elisset syl simpl simpr ex exlimdv mpd ) ADEZBDEZFZCDEZFZBAGHIZJIZKLZCMNZFZOPZUNQZORZUQURUNSEZVAVBURAGHTUAOUNSUBUCURUTUQOURUTUQURUTFURUQURUTUDUMUQUEUCUFUGUH $.
$}
