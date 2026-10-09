$( tests/stdlib/calculus/integral-is-real, elaborated from tests/stdlib/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A s $.
  $d B s $.
  $d C s $.
  $d D s $.
  tests.stdlib.calculus.integral-is-real $p |- ( ( ( ( ( ( A e. RR /\ B e. RR ) /\ A < B ) /\ C : ( A [,] B ) --> RR ) /\ C e. ( ( A [,] B ) -cn-> RR ) ) /\ D e. ( A [,] B ) ) -> S_ [ A -> D ] ( C ` s ) _d s e. RR ) $=
    ( cr wcel wa clt wbr cicc co wf ccncf simpl id syl simpr gditgre ) AFGZBFGZHZABIJZHZABKLZFCMZHZCUEFNLZGZHZDUEGZHZEABDCULUJTUJUKOZUJUGTUGUIOZUGUDTUDUFOZUDUBTUBUCOZUBTTTUAOTPQQQQQULUJUAUMUJUGUAUNUGUDUAUOUDUBUAUPTUARQQQQULUJUCUMUJUGUCUNUGUDUCUOUBUCRQQQULUJUFUMUJUGUFUNUDUFRQQULUJUIUMUGUIRQUJUKRS $.
$}
