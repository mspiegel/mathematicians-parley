$( tests/stdlib/geometry/perpendicular-foot, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/geometry/perpendicular-foot.mm $]

${
  $d A m $.
  $d B m $.
  $d C m $.
  tests.stdlib.geometry.perpendicular-foot $p |- ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ ( ( ( -. A = B /\ -. B = C ) /\ -. A = C ) /\ -. ( ( C - A ) / ( B - A ) ) e. RR ) ) -> E. m e. CC ( ( ( ( B = C \/ ( ( m - B ) / ( C - B ) ) e. RR ) /\ -. A = m ) /\ ( -. m = B -> ( abs ` ( ( A - m ) ang ( B - m ) ) ) = ( ( ; 9 0 x. _pi ) / ; ; 1 8 0 ) ) ) /\ ( -. m = C -> ( abs ` ( ( A - m ) ang ( C - m ) ) ) = ( ( ; 9 0 x. _pi ) / ; ; 1 8 0 ) ) ) ) $=
    ( cc wcel wa wceq wn cmin co cdiv cr cv wo cang cabs cfv c9 cc0 cdc cpi cmul c1 c8 wi wrex simpl id syl simpr jca stdlib.geometry.perpendicular-foot ) AEFZBEFZGZCEFZGZABHZIZBCHZIZGZACHZIZGZCAJKZBAJKZLKZMFZIZGZGZVMVADNZBJKCBJKLKMFOAVNHIGVNBHIAVNJKZBVNJKPKQRSTUAZUBUCKZUDUEUAZTUAZLKZHUFGVNCHIVOCVNJKPKQRVTHUFGDEUGVMURVLVMUPUQVMUNUOVMURUNURVLUHZURUPUNUPUQUHZUPUNUNUNUOUHUNUIUJUJUJVMURUOWAURUPUOWBUNUOUKUJUJULVMURUQWAUPUQUKUJULURVLUKULABCDUMUJ $.
$}
