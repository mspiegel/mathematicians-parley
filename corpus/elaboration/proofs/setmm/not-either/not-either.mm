$( proofs/setmm/not-either/not-either, elaborated from proofs/setmm/not-either.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  proofs.setmm.not-either.not-either $p |- ( ( A e. RR /\ B e. RR ) -> ( -. ( A = 0 \/ B = 0 ) <-> ( -. A = 0 /\ -. B = 0 ) ) ) $=
    ( cr wcel wa cc0 wceq wo wn simpr orc syl simpl pm2.21dd ex pm2.01d olc jca wi orel2 mpd eqcomd simpld impbida ) ACDZBCDZEZAFGZBFGZHZIZUHIZUIIZEZUGUKEZULUMUOUHUOUHULUOUHEZUJULUPUHUJUOUHJUHUIKLUPUOUKUOUHMUGUKJZLNOPUOUIUOUIUMUOUIEZUJUMURUIUJUOUIJUIUHQLURUOUKUOUIMUQLNOPRUGUNEZUJUSUJUKUSUJEZUHUKUTFAUTAFUTUJUHUSUJJUTUMUJUHSUTUNUMUTUSUNUSUJMZUGUNJZLZULUMJLUIUHTLUAUBUBUTULUMVCUCNOPUD $.
$}
