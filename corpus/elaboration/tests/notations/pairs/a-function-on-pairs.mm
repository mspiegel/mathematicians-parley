$( tests/notations/pairs/a-function-on-pairs, elaborated from tests/notations/pairs.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d x y $.
  $d A x y $.
  tests.notations.pairs.a-function-on-pairs $p |- ( ( A : ( RR X. RR ) --> RR /\ A. x e. RR A. y e. RR ( x A y ) = ( x + y ) ) -> ( 1 A 2 ) = 3 ) $=
    ( cr cxp wf cv co caddc wceq wral wa c1 c2 c3 simpr wcel wi 1re a1i id oveq1d eqeq12d ralbidv rspcv syl mpd 2re oveq2d eqid oveq12i 1p2e3 eqtri eqtr4i eqtrd ) DDEZDCFZAGZBGZCHZURUSIHZJZBDKZADKZLZMNCHZMNIHZOVEMUSCHZMUSIHZJZBDKZVFVGJZVEVDVKUQVDPVEMDQZVDVKRVMVESTVCVKAMDURMJZVBVJBDVNUTVHVAVIVNURMUSCVNUAZUBVNURMUSIVOUBUCUDUEUFUGVENDQZVKVLRVPVEUHTVJVLBNDUSNJZVHVFVIVGVQUSNMCVQUAZUIVQUSNMIVRUIUCUEUFUGVGOJVEVGOOVGVGOMMNNIMUJNUJUKULUMOUJUNTUO $.
$}
