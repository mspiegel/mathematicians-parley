$( tests/stdlib/reasoning/iff-not-from-right, elaborated from tests/stdlib/reasoning.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.reasoning.iff-not-from-right $p |- ( ( ( A e. RR /\ ( A = 0 <-> ( A ^ 2 ) = 0 ) ) /\ -. ( A ^ 2 ) = 0 ) -> -. A = 0 ) $=
    ( cr wcel cc0 wceq c2 cexp co wb wa wn simpr simpl syl mtbird ) ABCZADEZAFGHZDEZIZJZSKZJZQSUAUBLUCUATUAUBMPTLNO $.
$}
