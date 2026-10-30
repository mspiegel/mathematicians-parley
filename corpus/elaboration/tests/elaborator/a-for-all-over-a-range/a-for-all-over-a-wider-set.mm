$( tests/elaborator/a-for-all-over-a-range/a-for-all-over-a-wider-set, elaborated from tests/elaborator/a-for-all-over-a-range.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d i j $.
  $d A i j $.
  $d B i j $.
  tests.elaborator.a-for-all-over-a-range.a-for-all-over-a-wider-set $p |- ( ( ( A e. NN /\ B e. RR ) /\ A. i e. NN ( i / B ) e. RR ) -> sum_ j e. ( 1 ... ( A + 1 ) ) ( j / B ) = ( sum_ j e. ( 1 ... A ) ( j / B ) + ( ( A + 1 ) / B ) ) ) $=
    ( cn wcel cr wa cv cdiv co wral c1 caddc cuz cfv simpl id syl elnnuz sylib cfz cc simpr wi elfznn wceq oveq1d eleq1d rspcv mpd recn fsump1 ) AEFZBGFZHZCIZBJKZGFZCELZHZDIZBJKZAMNKZBJKDMAVAUNAMOPFVAUPUNUPUTQUPUNUNUNUOQUNRSSATUAVAVBMVDUBKZFZHZVCGFZVCUCFVGUTVHVGVAUTVAVFQUPUTUDSVGVBEFZUTVHUEVGVFVIVAVFUDVBVDUFSUSVHCVBEUQVBUGZURVCGVJUQVBBJVJRUHUIUJSUKVCULSVBVDUGZVBVDBJVKRUHUM $.
$}
