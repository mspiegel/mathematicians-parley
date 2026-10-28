$( tests/elaborator/listed-sets-in-any-order/a-pair-from-lines, elaborated from tests/elaborator/listed-sets-in-any-order.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/sets/subset-antisymmetric.mm $]

${
  tests.elaborator.listed-sets-in-any-order.a-pair-from-lines $p |- ( ( ( ( ( A e. _V /\ B e. _V ) /\ C e. _V ) /\ { B , C } C_ A ) /\ A C_ { B , C } ) -> A = { C , B } ) $=
    ( cvv wcel wa cpr wss wceq simpl id syl prex a1i jca simpr stdlib.sets.subset-antisymmetric eqcomd wb eqcom prcom eqeq2d bitrd mpbid ) ADEZBDEZFZCDEZFZBCGZAHZFZAUJHZFZUJAIZACBGZIZUNAUJUNUEUJDEZFZUMFZUKFAUJIZUNUTUKUNUSUMUNUEURUNULUEULUMJZULUIUEUIUKJUIUGUEUGUHJUGUEUEUEUFJUEKLLLLURUNBCMNOULUMPOUNULUKVBUIUKPLOAUJQLRUNUOVAUQUOVASUNUJATNUNUJUPAUNUPUJUPUJIUNCBUANRUBUCUD $.
$}
