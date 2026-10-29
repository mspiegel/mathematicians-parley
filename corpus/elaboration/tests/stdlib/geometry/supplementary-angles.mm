$( tests/stdlib/geometry/supplementary-angles, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.supplementary-angles $p |- ( ( ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. CC ) /\ ( A =/= B /\ ( ( C - B ) / ( A - B ) ) e. RR /\ ( ( C - B ) / ( A - B ) ) < 0 ) ) /\ -. D = B ) /\ -. D = A ) /\ -. D = C ) -> ( ( abs ` ( ( A - B ) ang ( D - B ) ) ) + ( abs ` ( ( D - B ) ang ( C - B ) ) ) ) = ( ( ; ; 1 8 0 x. _pi ) / ; ; 1 8 0 ) ) $=
    ( cc wcel wa wne cmin co cdiv cr cc0 clt wbr w3a wceq wn cang cabs cfv caddc c1 c8 cdc cpi cmul simpl simpr syl neqcomd wb df-ne a1i eqcom notbid bitrd bicomd mpbid wi id jca gsupp mpd ) AEFZBEFZGZCEFZGZDEFZGZABHZCBIJZABIJZKJZLFZVOMNOZPZGZDBQZRZGZDAQZRZGZDCQZRZGZDBHZVNDBIJZSJZTUAZWJVMSJZTUAZUBJZUCUDUEZMUEZUFUGJZWQKJZQZWHBDQZRZWIWHDBWHWEWAWEWGUHZWEWBWAWBWDUHZVSWAUIUJUJUKWHWIXBWHWIWAXBWIWAULWHDBUMUNWHVTXAVTXAULWHDBUOUNUPUQURUSWHVRWIWTUTZWHWEVRXCWEWBVRXDWBVSVRVSWAUHZVKVRUIUJUJUJWHVGVHVJGZGVRXEUTWHVGXGWHVEVFWHWEVEXCWEWBVEXDWBVSVEXFVSVKVEVKVRUHZVKVIVEVIVJUHZVIVGVEVGVHUHZVGVEVEVEVFUHVEVAUJUJUJUJUJUJUJWHWEVFXCWEWBVFXDWBVSVFXFVSVKVFXHVKVIVFXIVIVGVFXJVEVFUIUJUJUJUJUJUJVBWHVHVJWHWEVHXCWEWBVHXDWBVSVHXFVSVKVHXHVKVIVHXIVGVHUIUJUJUJUJUJWHWEVJXCWEWBVJXDWBVSVJXFVSVKVJXHVIVJUIUJUJUJUJVBVBABCDVCUJVDVD $.
$}
