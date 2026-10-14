$( tests/elaborator/a-letter-for-a-conjunction/a-conjunction-concluded-as-a-letter, elaborated from tests/elaborator/a-letter-for-a-conjunction.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.a-letter-for-a-conjunction.a-conjunction-concluded-as-a-letter $p |- ( ( ( A e. RR /\ ( A = 0 <-> ( 0 <_ A /\ A < 1 ) ) ) /\ A = 0 ) -> ( 0 <_ A /\ A < 1 ) ) $=
    ( cr wcel cc0 wceq cle wbr c1 clt wa wb simpr simpl syl mpbid ) ABCZADEZDAFGZAHIGZJZKZJZQJZQTUBQLUCUBUAUBQMPUALNO $.
$}
