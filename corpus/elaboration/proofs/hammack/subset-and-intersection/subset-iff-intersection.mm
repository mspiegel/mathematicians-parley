$( proofs/hammack/subset-and-intersection/subset-iff-intersection, elaborated from proofs/hammack/subset-and-intersection.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/sets/subset-antisymmetric.mm $]

${
  $d j k m $.
  $d A j k m $.
  $d B j k m $.
  proofs.hammack.subset-and-intersection.subset-iff-intersection $p |- ( ( A e. _V /\ B e. _V ) -> ( A C_ B <-> ( A i^i B ) = A ) ) $=
    ( cvv wcel wa wss cin wceq simpl id syl inex1g jca vm cv wral simpr wb elin a1i mpbid ralrimiva dfss3 mpbird vk ssel2 stdlib.sets.subset-antisymmetric vj eqcomd eleq2d impbida ) ACDZBCDZEZABFZABGZAHZUNUOEZUPCDZULEZUPAFZEZAUPFZEUQURVBVCURUTVAURUSULURULUSURUNULUNUOIZUNULULULUMIZULJZKZKZABCLKVHMURVANOZADZNUPPZURVJNUPURVIUPDZEZVJVIBDZEZVJVMVLVOURVLQVLVORVMVIABSTUAVJVNIKUBVAVKRURNUPAUCTUDMURVCUEOZUPDZUEAPZURVQUEAURVPADZEZVQVSVPBDZEZVTVSWAURVSQZVTUOVSEWAVTUOVSVTURUOURVSIUNUOQKWCMABVPUFKMVQWBRVTVPABSTUDUBVCVRRURUEAUPUCTUDMUPAUGKUNUQEZUOUHOZBDZUHAPZWDWFUHAWDWEADZEZWHWFEZWFWIWEUPDZWJWIWHWKWDWHQWIAUPWEWIUPAWIWDUQWDWHIUNUQQKUIUJUAWKWJRWIWEABSTUAWHWFQKUBUOWGRWDUHABUCTUDUK $.
$}
