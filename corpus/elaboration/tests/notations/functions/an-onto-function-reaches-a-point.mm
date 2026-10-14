$( tests/notations/functions/an-onto-function-reaches-a-point, elaborated from tests/notations/functions.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d x y $.
  $d A x y $.
  $d B x y $.
  $d C x y $.
  $d D x y $.
  tests.notations.functions.an-onto-function-reaches-a-point $p |- ( ( ( ( A e. _V /\ B e. _V ) /\ ( C : A --> B /\ C : A -onto-> B ) ) /\ D e. B ) -> E. x e. A D = ( C ` x ) ) $=
    ( cvv wcel wa wf wfo vy cv cfv wceq wrex wral simpl simpr syl wb dffo3 a1i mpbid wi id eqeq1d rexbidva rspcv mpd ) BFGZCFGZHZBCDIZBCDJZHZHZECGZHZKLZALZDMZNZABOZKCPZEVANZABOZURUMVDHZVDURUNVGURUOUNURUPUOUPUQQULUORSUMUNRSUNVGTURAKBCDUAUBUCUMVDRSURUQVDVFUDUPUQRVCVFKECUSENZVBVEABVHUTBGZHZUSEVAVJVHVHVHVIQVHUESUFUGUHSUI $.
$}
