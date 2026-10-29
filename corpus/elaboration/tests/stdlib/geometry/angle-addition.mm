$( tests/stdlib/geometry/angle-addition, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.angle-addition $p |- ( ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. CC ) /\ ( ( ( -. A = B /\ -. B = C ) /\ -. A = C ) /\ -. ( ( C - A ) / ( B - A ) ) e. RR ) ) /\ ( A =/= D /\ ( ( B - D ) / ( A - D ) ) e. RR /\ ( ( B - D ) / ( A - D ) ) < 0 ) ) /\ -. C = D ) -> ( ( abs ` ( ( A - C ) ang ( D - C ) ) ) + ( abs ` ( ( D - C ) ang ( B - C ) ) ) ) = ( abs ` ( ( A - C ) ang ( B - C ) ) ) ) $=
    ( cc wcel wa wceq wn cmin co cdiv cr wne cc0 clt wbr w3a cang cabs cfv caddc simpl simpr syl wi id jca gangadd mpd ) AEFZBEFZGZCEFZGZDEFZGZABHZIZBCHZIZGZACHZIZGZCAJKZBAJKZLKZMFZIZGZGZADNZBDJKZADJKZLKZMFZVPOPQZRZGZCDHZIZGZVSACJKZDCJKZSKZTUAZWEBCJKZSKZTUAZUBKZWDWHSKZTUAZHZWCVTVSVTWBUCZVLVSUDUEWCVKVSWNUFZWCVTVKWOVTVLVKVLVSUCZUQVKUDUEUEWCUMUNUPGZGVKWPUFWCUMWRWCUKULWCVTUKWOVTVLUKWQVLUQUKUQVKUCZUQUOUKUOUPUCZUOUMUKUMUNUCZUMUKUKUKULUCUKUGUEUEUEUEUEUEWCVTULWOVTVLULWQVLUQULWSUQUOULWTUOUMULXAUKULUDUEUEUEUEUEUHWCUNUPWCVTUNWOVTVLUNWQVLUQUNWSUQUOUNWTUMUNUDUEUEUEUEWCVTUPWOVTVLUPWQVLUQUPWSUOUPUDUEUEUEUHUHABCDUIUEUJUJ $.
$}
