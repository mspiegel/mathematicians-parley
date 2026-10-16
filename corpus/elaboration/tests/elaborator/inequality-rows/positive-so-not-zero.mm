$( tests/elaborator/inequality-rows/positive-so-not-zero, elaborated from tests/elaborator/inequality-rows.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.inequality-rows.positive-so-not-zero $p |- ( ( A e. RR /\ 0 < A ) -> -. A = 0 ) $=
    ( cr wcel cc0 clt wbr wa wne 0re a1i simpr ltne syl2anc neneqd ) ABCZDAEFZGZADQDBCZPADHRQIJOPKDALMN $.
$}
