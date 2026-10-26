$( tests/elaborator/an-interval-member-is-cited/a-closed-interval-member-is-cited, elaborated from tests/elaborator/an-interval-member-is-cited.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.elaborator.an-interval-member-is-cited.a-closed-interval-member-is-cited $p |- ( ( ( A e. RR /\ B e. RR ) /\ C e. ( A [,] B ) ) -> 0 <_ ( C ^ 2 ) ) $=
    ( cr wcel wa cicc co cc0 c2 cexp cle wbr simpl id syl simpr geliccre syl3anc sqge0 ) ADEZBDEZFZCABGHZEZFZCDEZICJKHLMUFUAUBUEUGUFUCUAUCUENZUCUAUAUAUBNUAOPPUFUCUBUHUAUBQPUCUEQABCRSCTP $.
$}
