$( proofs/setmm/not-both/not-both, elaborated from proofs/setmm/not-both.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  proofs.setmm.not-both.not-both $p |- ( ( A e. RR /\ B e. RR ) -> ( -. ( A = 0 /\ B = 0 ) <-> ( -. A = 0 \/ -. B = 0 ) ) ) $=
    ( cr wcel wa cc0 wceq wn wo simpl simpr syl jca pm2.21dd ex pm2.01d olc orc exmid a1i mpjaodan simpld simprd impbida ) ACDZBCDZEZAFGZBFGZEZHZUHHZUIHZIZUGUKEZUHUNULUOUHEZUMUNUPUIUPUIUMUPUIEZUJUMUQUHUIUQUPUHUPUIJZUOUHKLUPUIKMUQUPUKURUPUOUKUOUHJUGUKKLLNOPUMULQLUOULEULUNUOULKULUMRLUHULIUOUHSTUAUGUNEZULUKUMUSULEZUJUTUJUKUTUJEZUHUKVAUHUIUTUJKUBVAUTULUTUJJUSULKLNOPUSUMEZUJVBUJUKVBUJEZUIUKVCUHUIVBUJKUCVCVBUMVBUJJUSUMKLNOPUGUNKUAUD $.
$}
