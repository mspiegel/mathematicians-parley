$( tests/stdlib/geometry/area-positive, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.area-positive $p |- ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ ( ( ( -. A = B /\ -. B = C ) /\ -. A = C ) /\ -. ( ( C - A ) / ( B - A ) ) e. RR ) ) -> 0 < ( ( ( 1 / 2 ) x. ( ( abs ` ( B - C ) ) x. ( abs ` ( A - C ) ) ) ) x. ( abs ` ( sin ` ( ( B - C ) ang ( A - C ) ) ) ) ) ) $=
    ( cc wcel wa wceq wn cmin co cdiv cr cc0 c1 c2 cabs cfv cmul cang csin clt wbr simpr w3a wi simpl id syl 3jca gareapos mpd ) ADEZBDEZFZCDEZFZABGZHZBCGZHZFZACGZHZFZCAIJZBAIJZKJZLEZHZFZFZVJMNOKJZBCIJZPQZACIJZPQZRJZRJZVMVOSJZTQZPQZRJZUAUBZUPVJUCVKULUMUOUDVJWCUEVKULUMUOVKUPULUPVJUFZUPUNULUNUOUFZUNULULULUMUFULUGUHUHUHVKUPUMWDUPUNUMWEULUMUCUHUHVKUPUOWDUNUOUCUHUIABCUJUHUK $.
$}
