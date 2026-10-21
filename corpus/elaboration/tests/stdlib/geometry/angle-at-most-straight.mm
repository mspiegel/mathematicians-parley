$( tests/stdlib/geometry/angle-at-most-straight, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.angle-at-most-straight $p |- ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ -. A = B ) /\ -. C = B ) -> ( abs ` ( ( A - B ) ang ( C - B ) ) ) <_ ( ( ; ; 1 8 0 x. _pi ) / ; ; 1 8 0 ) ) $=
    ( cc wcel wa wceq wn cmin co cang cabs cfv c1 c8 cdc cc0 cpi cmul cdiv cle wbr simpl simpr syl jca w3a wi id 3jca gangle180 mpd ) ADEZBDEZFZCDEZFZABGZHZFZCBGZHZFZUSVBFZABIJZCBIJZKJZLMZNOPZQPZRSJZVJTJZUAUBZVCUSVBVCUTUSUTVBUCZUQUSUDUEUTVBUDUFVCUMUNUPUGVDVMUHVCUMUNUPVCUTUMVNUTUQUMUQUSUCZUQUOUMUOUPUCZUOUMUMUMUNUCUMUIUEUEUEUEVCUTUNVNUTUQUNVOUQUOUNVPUMUNUDUEUEUEVCUTUPVNUTUQUPVOUOUPUDUEUEUJABCUKUEUL $.
$}
