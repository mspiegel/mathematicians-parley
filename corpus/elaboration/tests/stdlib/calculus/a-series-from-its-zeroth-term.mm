$( tests/stdlib/calculus/a-series-from-its-zeroth-term, elaborated from tests/stdlib/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d i j k m p q $.
  $d A i j k m p q $.
  tests.stdlib.calculus.a-series-from-its-zeroth-term $p |- ( ( A : NN0 --> RR /\ ( m e. NN |-> sum_ j e. ( 0 ... m ) ( A ` j ) ) ~~> 3 ) -> sum_ j e. ( ZZ>= ` 0 ) ( A ` j ) = 3 ) $=
    ( cn0 cr wf cn cc0 cv cfz co cfv csu cmpt c3 cli wbr wa cuz vk wceq vi wcel simpl id syl simpr ffvelcdm syl2anc wb vp vq fveq2d cbvsumv a1i mpteq2ia oveq2d sumeq1d cbvmptv eqtri breq1i bitri mpbid sersumlim0 eqeq1i ) DEAFZCGHCIZJKZBIZALZBMZNZOPQZRZHSLZTIZALZTMZOUAZVOVJBMZOUAZVNVQOTUBVNVPDUCZRZVFWBVQEUCWCVNVFVNWBUDVNVFVFVFVMUDVFUEUFUFVNWBUGDEVPAUHUIVNVMUBGHUBIZJKZVQTMZNZOPQZVFVMUGVMWHUJVNVMUKGHUKIZJKZULIZALZULMZNZOPQWHVLWNOPVLCGVHWLULMZNWNCGVKWOVKWOUAVGGUCVHVJWLBULVIWKUAZVIWKAWPUEUMUNUOUPCUKGWOWMVGWIUAZVHWJWLULWQVGWIHJWQUEUQURUSUTVAWNWGOPWNUKGWJVQTMZNWGUKGWMWRWMWRUAWIGUCWJWLVQULTWKVPUAZWKVPAWSUEUMUNUOUPUKUBGWRWFWIWDUAZWJWEVQTWTWIWDHJWTUEUQURUSUTVAVBUOVCVDVSWAUJVNVSVOWDALZUBMZOUAWAVRXBOVOVQXATUBVPWDUAZVPWDAXCUEUMUNVEXBVTOVOXAVJUBBWDVIUAZWDVIAXDUEUMUNVEVBUOVC $.
$}
