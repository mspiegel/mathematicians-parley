$( tests/elaborator/reading-sentences/an-and-part-unfolded, elaborated from tests/elaborator/reading-sentences.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d k m n $.
  $d A k m n $.
  $d B k m n $.
  tests.elaborator.reading-sentences.an-and-part-unfolded $p |- ( ( ( A e. RR /\ B e. ZZ ) /\ ( A = 1 /\ 2 || B ) ) -> E. k e. ZZ B = ( 2 x. k ) ) $=
    ( cr wcel cz wa c1 wceq c2 cdvds wbr vn cv cmul co wrex simpr syl wb 2z a1i simpl jca divides mpbid vm id oveq1d eqeq1d cbvrexvw bitri cc 2cn zcn mulcom eqeq2d eqcom bitrd rexbidva bicomd ) ADEZBFEZGZAHIZJBKLZGZGZMNZJOPZBIZMFQZBJCNZOPZIZCFQZVHVFVLVHVGVFVDVGRVEVFRSVHJFEZVCGVFVLTVHVQVCVQVHUAUBVHVDVCVDVGUCVBVCRSUDMJBUESUFVHVLVMJOPZBIZCFQZVPVLVTTVHVLUGNZJOPZBIZUGFQVTVKWCMUGFVIWAIZVJWBBWDVIWAJOWDUHUIUJUKWCVSUGCFWAVMIZWBVRBWEWAVMJOWEUHUIUJUKULUBVHVPVTVHVOVSCFVHVMFEZGZVOBVRIZVSWGVNVRBWGJUMEZVMUMEZGVNVRIWGWIWJWIWGUNUBWGWFWJVHWFRVMUOSUDJVMUPSUQWHVSTWGBVRURUBUSUTVAUSUF $.
$}
