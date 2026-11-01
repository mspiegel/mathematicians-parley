$( tests/elaborator/an-instance-without-its-zero/an-instance-without-its-zero, elaborated from tests/elaborator/an-instance-without-its-zero.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A k $.
  tests.elaborator.an-instance-without-its-zero.an-instance-without-its-zero $p |- ( ( A : NN0 --> RR /\ A. k e. NN0 ( A ` ( k + 1 ) ) = ( ( A ` k ) + 2 ) ) -> ( A ` 1 ) = ( ( A ` 0 ) + 2 ) ) $=
    ( cn0 cr wf cv c1 caddc co cfv c2 wceq wral wa cc0 simpr wcel wi 0nn0 a1i id oveq1d fveq2d eqeq12d rspcv syl mpd cc ax-1cn addlid eqeq1d mpbid ) CDAEZBFZGHIZAJZUNAJZKHIZLZBCMZNZOGHIZAJZOAJZKHIZLZGAJZVELVAUTVFUMUTPVAOCQZUTVFRVHVASTUSVFBOCUNOLZUPVCURVEVIUOVBAVIUNOGHVIUAZUBUCVIUQVDKHVIUNOAVJUCUBUDUEUFUGVAVCVGVEVAVBGAVAGUHQZVBGLVKVAUITGUJUFUCUKUL $.
$}
