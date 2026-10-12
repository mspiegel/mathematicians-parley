$( tests/notations/sums/one-to-three-not-five, elaborated from tests/notations/sums.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ tests/notations/sums/one-to-three-summed.mm $]

${
  tests.notations.sums.one-to-three-not-five $p |- -. sum_ k e. ( 1 ... 3 ) k = 5 $=
    ( c1 c3 cfz co cv csu c5 wceq wn wtru wa c6 simpl tests.notations.sums.one-to-three-summed a1i syl eqcomd simpr eqtrd cr wcel clt wbr wne 5re 5lt6 jca ltne neneqd pm2.21dd ex pm2.01d mptru ) BCDEZAFZAGZHIZJZKURKURUSKURLZMHIUSUTMUQHUTUQMUTKUQMIZKURNVAKAOPQRKURSTUTMHUTHUAUBZHMUCUDZLMHUEUTVBVCVBUTUFPVCUTUGPUHHMUIQUJUKULUMUN $.
$}
