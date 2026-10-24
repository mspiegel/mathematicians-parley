$( tests/notations/powers/a-real-power-of-a-real-power, elaborated from tests/notations/powers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.notations.powers.a-real-power-of-a-real-power $p |- ( ( ( ( A e. RR /\ 0 < A ) /\ B e. RR ) /\ C e. RR ) -> ( A ^c ( B x. C ) ) = ( ( A ^c B ) ^c C ) ) $=
    ( cr wcel cc0 clt wbr wa crp cc w3a cmul co ccxp wceq simpl id syl simpr jca elrp sylibr recn 3jca cxpmul ) ADEZFAGHZIZBDEZIZCDEZIZAJEZUJCKEZLABCMNONABONCONPUMUNUJUOUMUIUNUMUGUHUMUKUGUKULQZUKUIUGUIUJQZUIUGUGUGUHQUGRSSSUMUKUHUPUKUIUHUQUGUHTSSUAAUBUCUMUKUJUPUIUJTSUMULUOUKULTCUDSUEABCUFS $.
$}
