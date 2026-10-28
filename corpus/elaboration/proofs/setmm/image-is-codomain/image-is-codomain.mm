$( proofs/setmm/image-is-codomain/image-is-codomain, elaborated from proofs/setmm/image-is-codomain.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]
$[ stdlib/sets/subset-antisymmetric.mm $]

${
  $d k m x y $.
  $d A k m x y $.
  $d B k m x y $.
  $d C k m x y $.
  proofs.setmm.image-is-codomain.image-is-codomain $p |- ( ( ( ( A e. _V /\ B e. _V ) /\ C : A --> B ) /\ A. y e. B E. x e. A y = ( C ` x ) ) -> ( C " A ) = B ) $=
    ( cvv wcel wa wf cv cfv wceq wrex wral cima wss simpl simpr syl id jca fex imaexg fimass vm vk wi eqeq1d rexbidva rspcv mpd wb fveq2d eqeq2d cbvrexvw a1i mpbid w3a ssid 3jca gfnfvima eqcomd eleq1d ex rexlimdva ralrimiva dfss3 mpbird stdlib.sets.subset-antisymmetric ) CFGZDFGZHZCDEIZHZBJZAJZEKZLZACMZBDNZHZECOZFGZVKHZWBDPZHZDWBPZHWBDLWAWFWGWAWDWEWAWCVKWAEFGZWCWAVMVJHWHWAVMVJWAVNVMVNVTQZVLVMRZSZWAVNVJWIVNVLVJVLVMQZVLVJVJVJVKQVJTSSSUACDFEUBSECFUCSWAVNVKWIVNVLVKWLVJVKRSSUAWAVMWEWKCDECUDSUAWAWGUEJZWBGZUEDNZWAWNUEDWAWMDGZHZWMUFJZEKZLZUFCMZWNWQWMVQLZACMZXAWQVTXCHXCWQVTXCWQWAVTWAWPQZVNVTRZSZWQVTXCXFWQWPVTXCUGWAWPRVSXCBWMDVOWMLZVRXBACXGVPCGZHZVOWMVQXIXGXGXGXHQXGTSUHUIUJSUKUAVTXCRSXCXAULWQXBWTAUFCVPWRLZVQWSWMXJVPWREXJTUMUNUOUPUQWQWTWNUFCWQWRCGZHZWTWNXLWTHZWSWBGZWNXMVMCCPZXKURXNXMVMXOXKXMXLVMXLWTQZXLWQVMWQXKQWQWAVMXDWKSSSXOXMCUSUPXMXLXKXPWQXKRSUTCDWRCEVASXMWSWMWBXMWMWSXLWTRVBVCUQVDVEUKVFWGWOULWAUEDWBVGUPVHUAWBDVIS $.
$}
