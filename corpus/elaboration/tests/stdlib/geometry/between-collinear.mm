$( tests/stdlib/geometry/between-collinear, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.between-collinear $p |- ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ ( B =/= A /\ ( ( C - A ) / ( B - A ) ) e. RR /\ ( ( C - A ) / ( B - A ) ) < 0 ) ) -> ( ( B - C ) / ( A - C ) ) e. RR ) $=
    ( cc wcel wa wne cmin co cdiv cr cc0 clt wbr w3a simpr wi simpl id syl 3jca gbetcol mpd ) ADEZBDEZFZCDEZFZBAGZCAHIZBAHIZJIZKEZULLMNZOZFZUOBCHIZACHIZJIZKEZUHUOPUPUDUEUGOUOUTQUPUDUEUGUPUHUDUHUORZUHUFUDUFUGRZUFUDUDUDUERUDSTTTUPUHUEVAUHUFUEVBUDUEPTTUPUHUGVAUFUGPTUAABCUBTUC $.
$}
