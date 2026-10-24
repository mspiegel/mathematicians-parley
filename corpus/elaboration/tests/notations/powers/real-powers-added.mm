$( tests/notations/powers/real-powers-added, elaborated from tests/notations/powers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.notations.powers.real-powers-added $p |- ( ( ( ( A e. RR /\ -. A = 0 ) /\ B e. RR ) /\ C e. RR ) -> ( A ^c ( B + C ) ) = ( ( A ^c B ) x. ( A ^c C ) ) ) $=
    ( cr wcel cc0 wceq wn wa cc wne w3a caddc co ccxp cmul simpl id syl recn simpr neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid jca 3jca cxpadd ) ADEZAFGZHZIZBDEZIZCDEZIZAJEZAFKZIZBJEZCJEZLABCMNONABONACONPNGVAVDVEVFVAVBVCVAUNVBVAUSUNUSUTQZUSUQUNUQURQZUQUNUNUNUPQUNRSSSATSVAFAGZHZVCVAAFVAUSUPVGUSUQUPVHUNUPUASSUBVAVCVJVAVCUPVJVCUPUCVAAFUDUEVAUOVIVAVIUOVIUOUCVAFAUFUEUGUHUIUGUJUKVAURVEVAUSURVGUQURUASBTSVAUTVFUSUTUACTSULABCUMS $.
$}
