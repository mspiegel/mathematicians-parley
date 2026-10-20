$( tests/elaborator/a-theorem-cited-at-a-raised-power/an-implication-used-as-a-conditional, elaborated from tests/elaborator/a-theorem-cited-at-a-raised-power.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.a-theorem-cited-at-a-raised-power.an-implication-used-as-a-conditional $p |- ( ( ( A e. RR /\ ( 1 < A -> 0 < A ) ) /\ 1 < A ) -> 0 < A ) $=
    ( cr wcel c1 clt wbr cc0 wi wa simpr simpl syl mpd ) ABCZDAEFZGAEFZHZIZOIZOPROJSRQROKNQJLM $.
$}
