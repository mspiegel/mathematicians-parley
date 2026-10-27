$( tests/stdlib/geometry/midpoint-exists, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A m $.
  $d B m $.
  tests.stdlib.geometry.midpoint-exists $p |- ( ( ( A e. CC /\ B e. CC ) /\ -. A = B ) -> E. m e. CC ( ( A =/= m /\ ( ( B - m ) / ( A - m ) ) e. RR /\ ( ( B - m ) / ( A - m ) ) < 0 ) /\ ( abs ` ( A - m ) ) = ( abs ` ( m - B ) ) ) ) $=
    ( cc wcel wa wceq wn wne cv cmin co cdiv cr cc0 clt wbr w3a cabs cfv wrex simpl id syl simpr jca neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid gmidex ) ADEZBDEZFZABGZHZFZUSABIZFACJZIBVDKLZAVDKLZMLZNEVGOPQRVFSTVDBKLSTGFCDUAVBUSVCVBUQURVBUSUQUSVAUBZUSUQUQUQURUBUQUCUDUDVBUSURVHUQURUEUDUFVBBAGZHZVCVBABUSVAUEUGVBVCVJVBVCVAVJVCVAUHVBABUIUJVBUTVIVBVIUTVIUTUHVBBAUKUJULUMUNULUOUFCABUPUD $.
$}
