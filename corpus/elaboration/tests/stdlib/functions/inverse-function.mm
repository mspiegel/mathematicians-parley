$( tests/stdlib/functions/inverse-function, elaborated from tests/stdlib/functions.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.functions.inverse-function $p |- ( ( ( ( A e. _V /\ B e. _V ) /\ ( C : A --> B /\ C : A -1-1-> B ) ) /\ ( C " A ) = B ) -> `' C : B --> A ) $=
    ( cvv wcel wa wf wf1 cima wceq ccnv simpl simpr syl jca gf1cnvf ) ADEZBDEZFZABCGZABCHZFZFZCAIZBJZFZUAUEFBACKGUFUAUEUFUBUAUFUCUBUCUELSUBMNTUAMNUCUEMOABCPN $.
$}
