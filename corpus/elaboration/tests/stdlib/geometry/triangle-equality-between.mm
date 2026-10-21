$( tests/stdlib/geometry/triangle-equality-between, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.triangle-equality-between $p |- ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ -. A = B ) /\ -. C = B ) /\ ( ( abs ` ( A - B ) ) + ( abs ` ( B - C ) ) ) = ( abs ` ( A - C ) ) ) -> ( A =/= B /\ ( ( C - B ) / ( A - B ) ) e. RR /\ ( ( C - B ) / ( A - B ) ) < 0 ) ) $=
    ( cc wcel wa wceq wn cmin co cabs cfv caddc wne cdiv cr cc0 clt wbr w3a simpr wi simpl syl neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid jca id 3jca gtrieq mpd ) ADEZBDEZFZCDEZFZABGZHZFZCBGZHZFZABIJZKLZBCIJZKLZMJZACIJZKLZGZFZVQABNZCBIJZVJOJZPEZWAQRSZTZVIVQUAVRVSCBNZFZVQWDUBZVRVSWEVRBAGZHZVSVRABVRVIVEVIVQUCZVIVFVEVFVHUCZVCVEUAUDUDUEVRVSWIVRVSVEWIVSVEUFVRABUGUHVRVDWHVRWHVDWHVDUFVRBAUIUHUJUKULUJUMVRBCGZHZWEVRCBVRVIVHWJVFVHUAUDUEVRWEWMVRWEVHWMWEVHUFVRCBUGUHVRVGWLVGWLUFVRCBUIUHUKULUJUMUNVRUSUTVBTWFWGUBVRUSUTVBVRVIUSWJVIVFUSWKVFVCUSVCVEUCZVCVAUSVAVBUCZVAUSUSUSUTUCUSUOUDUDUDUDUDVRVIUTWJVIVFUTWKVFVCUTWNVCVAUTWOUSUTUAUDUDUDUDVRVIVBWJVIVFVBWKVFVCVBWNVAVBUAUDUDUDUPABCUQUDURUR $.
$}
