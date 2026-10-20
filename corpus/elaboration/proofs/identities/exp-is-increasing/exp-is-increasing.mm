$( proofs/identities/exp-is-increasing/exp-is-increasing, elaborated from proofs/identities/exp-is-increasing.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  proofs.identities.exp-is-increasing.exp-is-increasing $p |- ( ( ( A e. RR /\ B e. RR ) /\ A < B ) -> ( exp ` A ) < ( exp ` B ) ) $=
    ( cr wcel wa clt wbr ce cfv clog wceq simpl id syl relogef simpr eqbrtrd eqcomd breqtrd crp wb cc0 reefcl efgt0 jca elrp sylibr logltb mpbird ) ACDZBCDZEZABFGZEZAHIZBHIZFGZUOJIZUPJIZFGZUNURBUSFUNURABFUNUJURAKUNULUJULUMLZULUJUJUJUKLZUJMZNZNZAONULUMPQUNUSBUNUKUSBKUNULUKVAUJUKPZNZBONRSUNUOTDZUPTDZEUQUTUAUNVHVIUNUOCDZUBUOFGZEVHUNVJVKUNUJVJVEAUCNUNUJVKVEAUDNUEUOUFUGUNUPCDZUBUPFGZEVIUNVLVMUNUKVLVGBUCNUNUKVMVGBUDNUEUPUFUGUEUOUPUHNUI $.
$}
