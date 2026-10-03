$( tests/elaborator/product-order/distances-out-of-order, elaborated from tests/elaborator/product-order.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.elaborator.product-order.distances-out-of-order $p |- ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. CC ) -> ( ( abs ` ( C - D ) ) x. ( abs ` ( A - B ) ) ) e. RR ) $=
    ( cc wcel wa cmin co cabs cfv cmul cr simpl simpr syl wi id gdistre mpd remulcld wceq recn jca mulcom eqcomd eleq1d mpbid ) AEFZBEFZGZCEFZGZDEFZGZABHIZJKZCDHIZJKZLIZMFUSUQLIZMFUOUQUSUOUJUQMFZUOUMUJUMUNNZUMUKUJUKULNZUIUJOZPZPZUOUIUJVBQZUOUMUIVCUMUKUIVDUKUIUIUIUJNZUIRZPZPZPZABSZPZTZUOUNUSMFZUMUNOZUOULUNVQQZUOUMULVCUKULOZPZCDSZPZTZUAUOUTVAMUOVAUTUOUSEFZUQEFZGVAUTUBUOWEWFUOVQWEWDUSUCPUOVBWFVPUQUCPUDUSUQUEPUFUGUH $.
$}
