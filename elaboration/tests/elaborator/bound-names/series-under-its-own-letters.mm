$( tests/elaborator/bound-names/series-under-its-own-letters, elaborated from tests/elaborator/bound-names.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d i j k n $.
  seriesun $p |- ( ( n e. NN |-> sum_ k e. ( 1 ... n ) ( 1 / ( k x. ( k + 1 ) ) ) ) ~~> 1 -> sum_ k e. ( ZZ>= ` 1 ) ( 1 / ( k x. ( k + 1 ) ) ) = 1 ) $=
    ( cn c1 cv cfz co caddc cmul cdiv csu cmpt cli wbr cuz cfv vj wceq vi wcel wa cr wral simpl 1re a1i syl simpr nnre readdcld remulcld cc0 wne 1nn nnaddcld nnmulcld nnne0 redivcld ralrimiva id oveq1d oveq12d oveq2d eleq1d cbvralvw sylib wi rspcv mpd cbvsumv mpteq2ia sumeq1d cbvmptv eqtri breq1d mpbid sersumlim eqeq1d ) BCDBEZFGZDAEZWADHGZIGZJGZAKZLZDMNZDOPZDQEZWIDHGZIGZJGZQKZDRWHWDAKZDRWGWLDQSWGWICTZUAZWDUBTZACUCZWLUBTZWPWGWRWGWOUDZWGWSQCUCWRWGWSQCWPDWKWPWGDUBTZWTXAWGUEUFZUGZWPWIWJWPWOWIUBTZWGWOUHZWIUIZUGZWPWIDXGXCUJUKWPWKCTWKULUMWPWIWJXEWPWIDXEDCTWPUNUFUOUPWKUQUGURUSWSWQQACWIWARZWLWDUBXHWKWCDJXHWIWAWJWBIXHUTZXHWIWADHXIVAZVBZVCZVDVEVFUGWPWOWRWSVGXEWQWSAWICWAWIRZWDWLUBXMWCWKDJXMWAWIWBWJIXMUTZXMWAWIDHXNVAZVBZVCZVDVHUGVIWGWGSCDSEZFGZWLQKZLZDMNWGUTWGWFYADMWFYARWGWFBCVTWLQKZLYABCWEYBWEYBRVSCTVTWDWLAQXQVJUFVKBSCYBXTVSXRRZVTXSWLQYCVSXRDFYCUTVCVLVMVNUFVOVPVQWGWMWNDWMWNRWGWHWLWDQAXLVJUFVRVP $.
$}
