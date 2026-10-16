$( tests/elaborator/transitivity/a-chain-through-a-define, elaborated from tests/elaborator/transitivity.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A m $.
  $d B m $.
  $d C m $.
  tests.elaborator.transitivity.a-chain-through-a-define $p |- ( ( ( ( ( A e. RR /\ B e. RR ) /\ C e. RR ) /\ ( A + 1 ) <_ B ) /\ B < C ) -> ( A + 1 ) < C ) $=
    ( cr wcel wa c1 caddc co cle wbr clt vm cv wceq wex cvv ovex a1i elisset syl simpr simpl id 1re readdcld eqeltrd eqbrtrd lelttrd breq1d mpbid ex exlimdv mpd ) ADEZBDEZFZCDEZFZAGHIZBJKZFZBCLKZFZMNZUTOZMPZUTCLKZVDUTQEZVGVIVDAGHRSMUTQTUAVDVFVHMVDVFVHVDVFFZVECLKVHVJVEBCVJVEUTDVDVFUBZVJAGVJVDUOVDVFUCZVDVBUOVBVCUCZVBUSUOUSVAUCZUSUQUOUQURUCZUQUOUOUOUPUCUOUDUAUAUAUAUAGDEVJUESUFUGVJVDUPVLVDVBUPVMVBUSUPVNUSUQUPVOUOUPUBUAUAUAUAVJVDURVLVDVBURVMVBUSURVNUQURUBUAUAUAVJVEUTBJVKVJVDVAVLVDVBVAVMUSVAUBUAUAUHVJVDVCVLVBVCUBUAUIVJVEUTCLVKUJUKULUMUN $.
$}
