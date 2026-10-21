$( tests/stdlib/geometry/distance-positive, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.distance-positive $p |- ( ( ( A e. CC /\ B e. CC ) /\ -. A = B ) -> 0 < ( abs ` ( A - B ) ) ) $=
    ( cc wcel wa wceq wn wne cc0 cmin co cabs cfv clt wbr simpr neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid wi simpl syl id gdistpos mpd ) ACDZBCDZEZABFZGZEZABHZIABJKZLMZNOZUQBAFZGZURUQABUNUPPQUQURVCUQURUPVCURUPRUQABSTUQUOVBUQVBUOVBUORUQBAUATUBUCUDUBUEUQUMURVAUFZUQUNUMUNUPUGZULUMPUHUQULUMVDUFUQUNULVEUNULULULUMUGULUIUHUHABUJUHUKUK $.
$}
