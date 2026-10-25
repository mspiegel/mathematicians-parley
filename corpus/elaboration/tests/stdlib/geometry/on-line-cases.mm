$( tests/stdlib/geometry/on-line-cases, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.on-line-cases $p |- ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ -. B = C ) /\ ( B = C \/ ( ( A - B ) / ( C - B ) ) e. RR ) ) -> ( ( ( ( A = B \/ ( B =/= A /\ ( ( C - A ) / ( B - A ) ) e. RR /\ ( ( C - A ) / ( B - A ) ) < 0 ) ) \/ A = C ) \/ ( B =/= C /\ ( ( A - C ) / ( B - C ) ) e. RR /\ ( ( A - C ) / ( B - C ) ) < 0 ) ) \/ ( A =/= B /\ ( ( C - B ) / ( A - B ) ) e. RR /\ ( ( C - B ) / ( A - B ) ) < 0 ) ) ) $=
    ( cc wcel wa wceq wn cmin co cdiv cr wo wne cc0 clt wbr w3a simpr wi simpl syl neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid id 3jca gonline mpd ) ADEZBDEZFZCDEZFZBCGZHZFZVAABIJZCBIJZKJZLEZMZFZVHABGZBANZCAIJZBAIJZKJZLEZVNOPQZRZMZACGZMZBCNZACIJZBCIJZKJZLEZWDOPQZRZMZABNZVEVDKJZLEZWJOPQZRZMZVCVHSVIWAVHWNTZVICBGZHZWAVIBCVIVCVBVCVHUAZUTVBSUBUCVIWAWQVIWAVBWQWAVBUDVIBCUEUFVIVAWPVIWPVAWPVAUDVICBUGUFUHUIUJUHUKVIUPUQUSRWAWOTVIUPUQUSVIVCUPWRVCUTUPUTVBUAZUTURUPURUSUAZURUPUPUPUQUAUPULUBUBUBUBVIVCUQWRVCUTUQWSUTURUQWTUPUQSUBUBUBVIVCUSWRVCUTUSWSURUSSUBUBUMABCUNUBUOUO $.
$}
