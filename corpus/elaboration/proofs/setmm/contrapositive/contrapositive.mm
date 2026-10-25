$( proofs/setmm/contrapositive/contrapositive, elaborated from proofs/setmm/contrapositive.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  proofs.setmm.contrapositive.contrapositive $p |- ( ( A e. RR /\ B e. RR ) -> ( ( A = 0 -> B = 0 ) -> ( -. B = 0 -> -. A = 0 ) ) ) $=
    ( cr wcel wa cc0 wceq wi wn simpr simpl syl mpd eqcomd pm2.21dd ex pm2.01d ) ACDZBCDZEZAFGZBFGZHZUBIZUAIZHTUCEZUDUEUFUDEZUAUGUAUEUGUAEZUBUEUHFBUHBFUHUAUBUGUAJUHUGUCUGUAKZUGUFUCUFUDKTUCJLLMNNUHUGUDUIUFUDJLOPQPP $.
$}
