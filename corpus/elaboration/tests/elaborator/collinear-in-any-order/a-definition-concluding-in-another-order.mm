$( tests/elaborator/collinear-in-any-order/a-definition-concluding-in-another-order, elaborated from tests/elaborator/collinear-in-any-order.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.elaborator.collinear-in-any-order.a-definition-concluding-in-another-order $p |- ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ ( ( ( -. A = B /\ -. B = C ) /\ -. A = C ) /\ -. ( ( C - A ) / ( B - A ) ) e. RR ) ) -> -. ( B = C \/ ( ( A - B ) / ( C - B ) ) e. RR ) ) $=
    ( cc wcel wa wceq wn cmin co cdiv cr wo simpr wb gtridef a1i mpbid syl w3a wi simpl id 3jca gcolrotate syld mtod ) ADEZBDEZFZCDEZFZABGZHZBCGZHZFZACGZHZFZCAIJZBAIJZKJZLEZHZFZFZUOABIJZCBIJZKJZLEZMZUMVDMZVGUTVMHZFZVNVGVFVOULVFNVFVOOVGABCPQRUTVNNSVGVLCAGZBCIJZACIJZKJZLEZMZVMVGUIUKUHTVLWAUAVGUIUKUHVGULUIULVFUBZULUJUIUJUKUBZUHUINZSZSZVGULUKWBUJUKNZSZVGULUHWBULUJUHWCUJUHUHUHUIUBZUHUCZSZSZSZUDBCAUESVGUKUHUITWAVMUAVGUKUHUIWHWMWFUDCABUESUFUG $.
$}
