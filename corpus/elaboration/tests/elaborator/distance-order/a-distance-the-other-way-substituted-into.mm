$( tests/elaborator/distance-order/a-distance-the-other-way-substituted-into, elaborated from tests/elaborator/distance-order.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.distance-order.a-distance-the-other-way-substituted-into $p |- ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. RR ) /\ ( abs ` ( A - B ) ) = 3 ) /\ ( ( abs ` ( B - A ) ) + C ) = 5 ) -> ( 3 + C ) = 5 ) $=
    ( cc wcel wa cr cmin co cabs cfv c3 wceq caddc c5 simpr simpl syl eqcomd wb eqcom a1i id abssubd eqeq2d bitrd bicomd mpbid oveq1d eqeq1d ) ADEZBDEZFZCGEZFZABHIZJKZLMZFZBAHIZJKZCNIZOMZFZVCLCNIZOMUSVCPVDVBVEOVDVALCNVDLUQMZVALMZVDUQLVDUSURUSVCQZUOURPRSVDVGVFVDVGLVAMZVFVGVITVDVALUAUBVDVAUQLVDBAVDUSULVHUSUOULUOURQZUOUMULUMUNQZUKULPRRRVDUSUKVHUSUOUKVJUOUMUKVKUMUKUKUKULQUKUCRRRRUDUEUFUGUHUIUJUH $.
$}
