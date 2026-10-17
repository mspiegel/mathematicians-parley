$( proofs/hammack/image-of-preimage-of-image/image-of-preimage-of-image, elaborated from proofs/hammack/image-of-preimage-of-image.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]
$[ proofs/hammack/preimage-of-image/subset-of-preimage-of-image.mm $]

${
  $d k m s $.
  $d A k m s $.
  $d B k m s $.
  $d C k m s $.
  $d D k m s $.
  proofs.hammack.image-of-preimage-of-image.image-of-preimage-of-image $p |- ( ( ( ( A e. _V /\ B e. _V ) /\ C : A --> B ) /\ D e. ~P A ) -> ( C " ( `' C " ( C " D ) ) ) = ( C " D ) ) $=
    ( cvv wcel wa wf cpw ccnv cima wss wceq vk cv wral vs cfv wrex simpr wb simpl syl vm gelpreima mpbid ralrimiva dfss3 a1i mpbird jca gfvelima eqcomd eleq1d ex rexlimdva mpd id proofs.hammack.preimage-of-image.subset-of-preimage-of-image imass2 eqss sylibr ) AEFZBEFZGZABCHZGZDAIZFZGZCCJZCDKZKZKZVLLZVLVNLZGVNVLMVJVOVPVJVONOZVLFZNVNPZVJVRNVNVJVQVNFZGZVQQOZCRZMZQVMSZVRWAVTWEVJVTTWAVFVMALZGVTWEUAWAVFWFWAVJVFVJVTUBZVJVGVFVGVIUBZVEVFTZUCZUCZWAVJWFWGVJWFUDOZAFZUDVMPZVJWMUDVMVJWLVMFZGZWMWLCRZVLFZGZWMWPWOWSVJWOTWPVFWOWSUAWPVJVFVJWOUBWJUCABWLVLCUEUCUFWMWRUBUCUGWFWNUAVJUDVMAUHUIUJUCUKQABVQVMCULUCUFWAWDVRQVMWAWBVMFZGZWDVRXAWDGZWCVLFZVRXBWBAFZXCGZXCXBWTXEXBXAWTXAWDUBZWAWTTUCXBVFWTXEUAXBXAVFXFXAWAVFWAWTUBWKUCUCABWBVLCUEUCUFXDXCTUCXBWCVQVLXBVQWCXAWDTUMUNUFUOUPUQUGVOVSUAVJNVNVLUHUIUJVJDVMLZVPVJVJXGVJVGVIVJVEVFVJVCVDVJVGVCWHVGVEVCVEVFUBZVEVCVCVCVDUBVCURUCUCUCVJVGVDWHVGVEVDXHVCVDTUCUCUKWJUKVGVITUKABCDUSUCDVMCUTUCUKVNVLVAVB $.
$}
