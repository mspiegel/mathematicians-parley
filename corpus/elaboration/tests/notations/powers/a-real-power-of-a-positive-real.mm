$( tests/notations/powers/a-real-power-of-a-positive-real, elaborated from tests/notations/powers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.notations.powers.a-real-power-of-a-positive-real $p |- ( ( ( A e. RR /\ 0 < A ) /\ B e. RR ) -> 0 < ( A ^c B ) ) $=
    ( cr wcel cc0 clt wbr wa w3a ccxp co simpl id syl simpr 3jca gcxpgt0 ) ACDZEAFGZHZBCDZHZRSUAIEABJKFGUBRSUAUBTRTUALZTRRRSLRMNNUBTSUCRSONTUAOPABQN $.
$}
