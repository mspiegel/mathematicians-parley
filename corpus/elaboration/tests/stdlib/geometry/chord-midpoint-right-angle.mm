$( tests/stdlib/geometry/chord-midpoint-right-angle, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/geometry/chord-midpoint-right-angle.mm $]

${
  tests.stdlib.geometry.chord-midpoint-right-angle $p |- ( ( ( ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. CC ) /\ ( ( A =/= C /\ ( ( B - C ) / ( A - C ) ) e. RR /\ ( ( B - C ) / ( A - C ) ) < 0 ) /\ ( abs ` ( A - C ) ) = ( abs ` ( C - B ) ) ) ) /\ ( abs ` ( A - D ) ) = ( abs ` ( B - D ) ) ) /\ -. D = C ) /\ -. C = B ) /\ -. D = B ) -> ( abs ` ( ( D - C ) ang ( B - C ) ) ) = ( ( ; 9 0 x. _pi ) / ; ; 1 8 0 ) ) $=
    ( cc wcel wa wne cmin co cdiv cr cc0 clt wbr w3a cabs cfv wceq wn cang c9 cdc cpi cmul c1 c8 simpl id syl simpr jca stdlib.geometry.chord-midpoint-right-angle ) AEFZBEFZGZCEFZGZDEFZGZACHZBCIJZACIJZKJZLFZVDMNOZPZVCQRZCBIJZQRZSZGZGZADIJZQRZBDIJZQRZSZGZDCSZTZGZCBSZTZGZDBSZTZGZWHDCIJVBUAJQRUBMUCUDUEJUFUGUCMUCKJSWHWEWGWHWBWDWHVSWAWHVMVRWHUTVLWHURUSWHUPUQWHUNUOWHWEUNWEWGUHZWEWBUNWBWDUHZWBVSUNVSWAUHZVSVMUNVMVRUHZVMUTUNUTVLUHZUTURUNURUSUHZURUPUNUPUQUHZUPUNUNUNUOUHUNUIUJUJUJUJUJUJUJUJWHWEUOWIWEWBUOWJWBVSUOWKVSVMUOWLVMUTUOWMUTURUOWNURUPUOWOUNUOUKUJUJUJUJUJUJUJULWHWEUQWIWEWBUQWJWBVSUQWKVSVMUQWLVMUTUQWMUTURUQWNUPUQUKUJUJUJUJUJUJULWHWEUSWIWEWBUSWJWBVSUSWKVSVMUSWLVMUTUSWMURUSUKUJUJUJUJUJULWHWEVLWIWEWBVLWJWBVSVLWKVSVMVLWLUTVLUKUJUJUJUJULWHWEVRWIWEWBVRWJWBVSVRWKVMVRUKUJUJUJULWHWEWAWIWEWBWAWJVSWAUKUJUJULWHWEWDWIWBWDUKUJULWEWGUKULABCDUMUJ $.
$}
