$( tests/elaborator/a-chain-going-down/a-chain-going-down-from-an-equation, elaborated from tests/elaborator/a-chain-going-down.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.a-chain-going-down.a-chain-going-down-from-an-equation $p |- ( ( ( ( ( A e. RR /\ B e. RR ) /\ C e. RR ) /\ A = B ) /\ C <_ B ) -> C <_ A ) $=
    ( cr wcel wa wceq cle wbr simpr simpl syl eqcomd breqtrd ) ADEZBDEZFZCDEZFZABGZFZCBHIZFZCBAHUAUBJUCABUCUATUAUBKSTJLMN $.
$}
