$( tests/notations/numbers/abs-three, elaborated from tests/notations/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.notations.numbers.abs-three $p |- ( abs ` 3 ) = 3 $=
    ( c3 cabs cfv wceq wtru cr wcel cc0 cle wbr wa 3re a1i clt 3pos wi 0re ltle syl2anc mpd jca absid syl mptru ) ABCZADZEAFGZHAIJZKUFEUGUHUGELMZEHANJZUHUJEOMEHFGZUGUJUHPUKEQMUIHARSTUAAUBUCUD $.
$}
