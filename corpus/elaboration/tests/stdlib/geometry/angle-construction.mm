$( tests/stdlib/geometry/angle-construction, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A m $.
  $d B m $.
  $d C m $.
  $d D m $.
  tests.stdlib.geometry.angle-construction $p |- ( ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. RR ) /\ ( ( ( -. A = B /\ -. B = C ) /\ -. A = C ) /\ -. ( ( C - A ) / ( B - A ) ) e. RR ) ) /\ ( ( 0 x. _pi ) / ; ; 1 8 0 ) < D ) /\ D < ( ( ; ; 1 8 0 x. _pi ) / ; ; 1 8 0 ) ) -> E. m e. CC ( 0 < ( ( Im ` ( ( m - A ) / ( B - A ) ) ) x. ( Im ` ( ( C - A ) / ( B - A ) ) ) ) /\ ( abs ` ( ( B - A ) ang ( m - A ) ) ) = D ) ) $=
    ( gangconsm ) EABCDF $.
$}
