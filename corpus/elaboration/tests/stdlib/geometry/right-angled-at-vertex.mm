$( tests/stdlib/geometry/right-angled-at-vertex, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.right-angled-at-vertex $p |- ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ ( ( ( -. A = B /\ -. B = C ) /\ -. A = C ) /\ -. ( ( C - A ) / ( B - A ) ) e. RR ) ) /\ ( abs ` ( ( A - C ) ang ( B - C ) ) ) = ( ( ; 9 0 x. _pi ) / ; ; 1 8 0 ) ) -> ( ( ( ( -. A = B /\ -. B = C ) /\ -. A = C ) /\ -. ( ( C - A ) / ( B - A ) ) e. RR ) /\ ( ( ( C = A /\ ( abs ` ( ( B - A ) ang ( C - A ) ) ) = ( ( ; 9 0 x. _pi ) / ; ; 1 8 0 ) ) \/ ( C = B /\ ( abs ` ( ( A - B ) ang ( C - B ) ) ) = ( ( ; 9 0 x. _pi ) / ; ; 1 8 0 ) ) ) \/ ( C = C /\ ( abs ` ( ( A - C ) ang ( B - C ) ) ) = ( ( ; 9 0 x. _pi ) / ; ; 1 8 0 ) ) ) ) ) $=
    ( cc wcel wa wceq wn cmin co cdiv cr cang cabs cfv c9 cc0 cdc cpi cmul c1 c8 wo simpl simpr syl jca grightat3 sylibr ) ADEZBDEZFZCDEZFZABGZHZBCGZHZFZACGZHZFZCAIJZBAIJZKJZLEZHZFZFZACIJZBCIJZMJZNOZPQRZSTJZUAUBRZQRZKJZGZFZVHVSFVHCAGVDVCMJNOVRGFCBGABIJCBIJMJNOVRGFUCCCGVSFUCFVTVHVSVTVIVHVIVSUDUNVHUEUFVIVSUEUGABCUHUI $.
$}
