$( proofs/setmm/subset-of-union-and-difference/subset-of-union-and-difference, elaborated from proofs/setmm/subset-of-union-and-difference.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d k m $.
  $d A k m $.
  $d B k m $.
  $d C k m $.
  proofs.setmm.subset-of-union-and-difference.subset-of-union-and-difference $p |- ( ( ( A e. _V /\ B e. _V ) /\ C e. _V ) -> ( A C_ ( B u. C ) <-> ( A \ B ) C_ C ) ) $=
    ( cvv wcel wa cun wss cdif vm cv wral simpr wn simpl wb eldif a1i mpbid syl simprd pm2.21dd wo jca ssel2 elun mpjaodan ralrimiva dfss3 mpbird vk orc olc exmid impbida ) ADEZBDEZFZCDEZFZABCGZHZABIZCHZUTVBFZVDJKZCEZJVCLZVEVGJVCVEVFVCEZFZVFBEZVGVGVJVKFZVKVGVJVKMVLVFAEZVKNZVLVJVMVNFZVJVKOVJVIVOVEVIMZVIVOPZVJVFABQZRZSZTUAUBVJVGMVJVFVAEZVKVGUCZVJVBVMFWAVJVBVMVJVEVBVEVIOUTVBMTVJVOVMVTVMVNOTUDAVAVFUETWAWBPVJVFBCUFRSUGUHVDVHPVEJVCCUIRUJUTVDFZVBUKKZVAEZUKALZWCWEUKAWCWDAEZFZWDBEZWEWINZWHWIFZWEWIWDCEZUCZWKWIWMWHWIMWIWLULTWEWMPZWKWDBCUFZRUJWHWJFZWEWMWPWLWMWPVDWDVCEZFWLWPVDWQWPWHVDWHWJOZWHWCVDWCWGOUTVDMTTWPWQWGWJFZWPWGWJWPWHWGWRWCWGMTWHWJMUDWQWSPWPWDABQRUJUDVCCWDUETWLWIUMTWNWPWORUJWIWJUCWHWIUNRUGUHVBWFPWCUKAVAUIRUJUO $.
$}
