$( stdlib/geometry/circle-centre-apart, elaborated from corpus/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  stdlib.geometry.circle-centre-apart $p |- ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ -. A = B ) /\ ( abs ` ( A - C ) ) = ( abs ` ( B - C ) ) ) -> -. A = C ) $=
    ( cc wcel wa wceq wn cmin co cabs cfv simpr cc0 wb simpl syl wi id gdist0 mpd mpbird eqeq1d mpbid eqcomd eqcom a1i abssubd bitrd eqtrd neqcomd pm2.21dd ex pm2.01d ) ADEZBDEZFZCDEZFZABGZHZFZACIJZKLZBCIJZKLZGZFZACGZVHVIVIHZVHVIFZUTVJVKACBVHVIMZVKCBIJZKLZNGZCBGZVKNVFGZVOVKVFNVKVDNGZVFNGZVKVRVIVLVKURVRVIOZVKVHURVHVIPZVHVBURVBVGPZVBUSURUSVAPZUQURMZQZQZQZVKUOURVTRVKVHUOWAVHVBUOWBVBUSUOWCUSUQUOUQURPZUQUOUOUOUPPUOSQQQQQACTQUAUBVKVDVFNVKVHVGWAVBVGMQUCUDUEVKVQVSVOVQVSOVKNVFUFUGVKVFVNNVKVNVFVKCBWGVKVHUPWAVHVBUPWBVBUSUPWCUSUQUPWHUOUPMZQZQZQZQZUHUEUCUIUDVKUPVOVPOZWMVKURUPWNRWGCBTQUAUDUJVKBAVKABVKVHVAWAVHVBVAWBUSVAMQQUKUKULUMUN $.
$}
