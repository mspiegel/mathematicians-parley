$( tests/stdlib/geometry/perpendicular-by-right-angle, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.perpendicular-by-right-angle $p |- ( ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ -. A = B ) /\ -. C = B ) /\ -. A = C ) /\ ( abs ` ( ( A - B ) ang ( C - B ) ) ) = ( ( ; 9 0 x. _pi ) / ; ; 1 8 0 ) ) -> ( B =/= A /\ B =/= C /\ ( Re ` ( ( C - B ) / ( A - B ) ) ) = 0 ) ) $=
    ( cc wcel wa wceq wn cmin co cang cabs cfv c9 cc0 cdc cpi cmul c1 c8 cdiv wne cre w3a simpr wb simpl syl jca wi id 3jca gperp90 mpd mpbird ) ADEZBDEZFZCDEZFZABGZHZFZCBGZHZFZACGZHZFZABIJZCBIJZKJZLMZNOPZQRJZSTPZOPZUAJZGZFZBAUBZBCUBZVKVJUAJZUCMZOGZUDZVSVIVSUEVTVBVEFZWFVSUFZVTVBVEVTVIVBVIVSUGZVIVFVBVFVHUGZVFVCVBVCVEUGZUTVBUEUHUHUHVTVIVEWIVIVFVEWJVCVEUEUHUHUIVTUPUQUSUDWGWHUJVTUPUQUSVTVIUPWIVIVFUPWJVFVCUPWKVCUTUPUTVBUGZUTURUPURUSUGZURUPUPUPUQUGUPUKUHUHUHUHUHUHVTVIUQWIVIVFUQWJVFVCUQWKVCUTUQWLUTURUQWMUPUQUEUHUHUHUHUHVTVIUSWIVIVFUSWJVFVCUSWKVCUTUSWLURUSUEUHUHUHUHULABCUMUHUNUO $.
$}
