$( tests/stdlib/geometry/cosine-right-triangle, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.cosine-right-triangle $p |- ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ -. A = C ) /\ -. B = C ) /\ ( abs ` ( ( A - C ) ang ( B - C ) ) ) = ( ( ; 9 0 x. _pi ) / ; ; 1 8 0 ) ) -> ( abs ` ( B - C ) ) = ( ( abs ` ( B - A ) ) x. ( cos ` ( abs ` ( ( C - B ) ang ( A - B ) ) ) ) ) ) $=
    ( cc wcel wa wceq wn cmin co cang cabs cfv c9 cc0 cdc cpi cmul c1 c8 cdiv ccos simpr wi simpl syl jca w3a id 3jca gcosrt mpd ) ADEZBDEZFZCDEZFZACGZHZFZBCGZHZFZACIJZBCIJZKJZLMZNOPZQRJZSTPZOPZUAJZGZFZVMVELMZBAIJZLMZCBIJZABIJZKJZLMZUBMZRJZGZVCVMUCVNUSVBFZVMWDUDZVNUSVBVNVCUSVCVMUEZVCUTUSUTVBUEZUQUSUCUFUFVNVCVBWGUTVBUCUFUGVNUMUNUPUHWEWFUDVNUMUNUPVNVCUMWGVCUTUMWHUTUQUMUQUSUEZUQUOUMUOUPUEZUOUMUMUMUNUEUMUIUFUFUFUFUFVNVCUNWGVCUTUNWHUTUQUNWIUQUOUNWJUMUNUCUFUFUFUFVNVCUPWGVCUTUPWHUTUQUPWIUOUPUCUFUFUFUJABCUKUFULUL $.
$}
