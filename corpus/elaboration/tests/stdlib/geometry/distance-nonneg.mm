$( tests/stdlib/geometry/distance-nonneg, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.distance-nonneg $p |- ( ( A e. CC /\ B e. CC ) -> 0 <_ ( abs ` ( A - B ) ) ) $=
    ( cc wcel wa cc0 cmin co cabs cfv cle wbr simpr wi simpl id syl gdistnn mpd ) ACDZBCDZEZUAFABGHZIJZKLZTUAMUBTUAUENUBTTTUAOTPQABRQS $.
$}
