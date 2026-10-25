$( tests/elaborator/distance-order/a-distance-the-substitution-leaves-written-the-other-way, elaborated from tests/elaborator/distance-order.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.distance-order.a-distance-the-substitution-leaves-written-the-other-way $p |- ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. RR ) /\ C = 3 ) /\ ( ( abs ` ( A - B ) ) + C ) = 5 ) -> ( ( abs ` ( B - A ) ) + 3 ) = 5 ) $=
    ( cc wcel wa cr c3 wceq cmin co cabs cfv caddc c5 simpr simpl syl id abssubd eqcomd oveq12d eqeq1d mpbid ) ADEZBDEZFZCGEZFZCHIZFZABJKZLMZCNKZOIZFZUOBAJKZLMZHNKZOIUKUOPUPUNUSOUPUMURCHNUPURUMUPBAUPUKUFUKUOQZUKUIUFUIUJQZUIUGUFUGUHQZUEUFPRRRUPUKUEUTUKUIUEVAUIUGUEVBUGUEUEUEUFQUESRRRRTUAUPUKUJUTUIUJPRUBUCUD $.
$}
