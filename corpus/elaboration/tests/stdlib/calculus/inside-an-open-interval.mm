$( tests/stdlib/calculus/inside-an-open-interval, elaborated from tests/stdlib/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.calculus.inside-an-open-interval $p |- ( ( ( A e. RR /\ B e. RR ) /\ C e. ( A (,) B ) ) -> ( ( C e. RR /\ A < C ) /\ C < B ) ) $=
    ( cr wcel wa cioo co clt wbr w3a simpr simpl id syl gelioo2 mpbid simp1 simp2 jca simp3 ) ADEZBDEZFZCABGHZEZFZCDEZACIJZFCBIJZUGUHUIUGUHUIUJKZUHUGUFUKUDUFLZUGABCUGUDUBUDUFMZUDUBUBUBUCMZUBNZOZOZUGUDUCUMUBUCLZOZPZQZUHUIUJROUGUKUIVAUHUIUJSOTUGUKUJVAUHUIUJUAOT $.
$}
