$( tests/stdlib/geometry/angle-construction-unique, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A u $.
  $d B u $.
  $d C u $.
  $d D u $.
  $d E u $.
  tests.stdlib.geometry.angle-construction-unique $p |- ( ( ( ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. CC ) /\ E e. CC ) /\ ( ( ( -. A = B /\ -. B = C ) /\ -. A = C ) /\ -. ( ( C - A ) / ( B - A ) ) e. RR ) ) /\ 0 < ( ( Im ` ( ( D - A ) / ( B - A ) ) ) x. ( Im ` ( ( C - A ) / ( B - A ) ) ) ) ) /\ 0 < ( ( Im ` ( ( E - A ) / ( B - A ) ) ) x. ( Im ` ( ( C - A ) / ( B - A ) ) ) ) ) /\ ( abs ` ( ( B - A ) ang ( D - A ) ) ) = ( abs ` ( ( B - A ) ang ( E - A ) ) ) ) -> E e. { u e. CC | ( A = D \/ ( ( ( u - A ) / ( D - A ) ) e. RR /\ 0 <_ ( ( u - A ) / ( D - A ) ) ) ) } ) $=
    ( gangconsuniq ) ABCDEFG $.
$}
