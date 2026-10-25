$( tests/elaborator/distance-order/a-distance-the-other-way-restated, elaborated from tests/elaborator/distance-order.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.distance-order.a-distance-the-other-way-restated $p |- ( ( ( A e. CC /\ B e. CC ) /\ ( abs ` ( A - B ) ) = 3 ) -> ( abs ` ( B - A ) ) = 3 ) $=
    ( cc wcel wa cmin co cabs cfv c3 wceq simpr simpl syl id abssubd eqcomd eqeq1d mpbid ) ACDZBCDZEZABFGZHIZJKZEZUEBAFGZHIZJKUBUELUFUDUHJUFUHUDUFBAUFUBUAUBUEMZTUALNUFUBTUIUBTTTUAMTONNPQRS $.
$}
