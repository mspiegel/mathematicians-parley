$( tests/stdlib/geometry/distance-zero, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.distance-zero $p |- ( ( A e. CC /\ B e. CC ) -> ( ( abs ` ( A - B ) ) = 0 <-> A = B ) ) $=
    ( cc wcel wa cmin co cabs cfv cc0 wceq wb simpr wi simpl id syl gdist0 mpd ) ACDZBCDZEZUAABFGZHIZJKZABKZLZTUAMUBTUAUGNUBTTTUAOTPQABRQS $.
$}
