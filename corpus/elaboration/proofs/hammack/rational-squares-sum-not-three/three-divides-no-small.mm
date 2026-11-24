$( proofs/hammack/rational-squares-sum-not-three/three-divides-no-small, elaborated from proofs/hammack/rational-squares-sum-not-three.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  proofs.hammack.rational-squares-sum-not-three.three-divides-no-small $p |- ( ( A e. NN /\ A < 3 ) -> -. 3 || A ) $=
    ( cn wcel c3 clt wbr wa cdvds wn cle simpr cz wi 3z a1i simpl id syl jca dvdsle mpd cr wb nnre 3re ltnle syl2anc mpbid pm2.21dd ex pm2.01d ) ABCZADEFZGZDAHFZUNUOUOIZUNUOGZDAJFZUPUQUOURUNUOKUQDLCZULGUOURMUQUSULUSUQNOUQUNULUNUOPZUNULULULUMPZULQZRZRZSDATRUAUQUMURIZUQUNUMUTULUMKRUQAUBCZDUBCZUMVEUCUQULVFVDAUDRVGUQUEOADUFUGUHUIUJUK $.
$}
