$( tests/stdlib/sets/separation, elaborated from tests/stdlib/sets.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A x $.
  $d B x $.
  tests.stdlib.sets.separation $p |- ( ( A e. _V /\ B e. _V ) -> { x e. A | -. x e. B } e. _V ) $=
    ( cvv wcel wa cv wn crab simpl id syl rabexg ) BDEZCDEZFZNAGZCEZHZABIDEPNNNOJNKLSABDML $.
$}
