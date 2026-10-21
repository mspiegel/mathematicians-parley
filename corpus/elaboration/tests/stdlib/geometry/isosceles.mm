$( tests/stdlib/geometry/isosceles, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.geometry.isosceles $p |- ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ ( ( ( -. A = B /\ -. B = C ) /\ -. A = C ) /\ -. ( ( C - A ) / ( B - A ) ) e. RR ) ) /\ ( abs ` ( A - B ) ) = ( abs ` ( A - C ) ) ) -> ( ( ( ( -. A = B /\ -. B = C ) /\ -. A = C ) /\ -. ( ( C - A ) / ( B - A ) ) e. RR ) /\ ( ( ( abs ` ( A - B ) ) = ( abs ` ( A - C ) ) \/ ( abs ` ( B - A ) ) = ( abs ` ( B - C ) ) ) \/ ( abs ` ( C - A ) ) = ( abs ` ( C - B ) ) ) ) ) $=
    ( cc wcel wa wceq wn cmin co cdiv cr cabs cfv wo simpl simpr syl orc jca wb biid a1i mpbird ) ADEZBDEZFZCDEZFZABGZHZBCGZHZFZACGZHZFZCAIJZBAIJZKJZLEZHZFZFZABIJZMNZACIJZMNZGZFZVCVIUSMNZBCIJZMNZGZOZURMNZCBIJZMNZGZOZFZWAVJVCVTVJVDVCVDVIPUIVCQRVJVOVTVJVIVOVDVIQVIVNSRVOVSSRTWAWAUAVJWAUBUCUD $.
$}
