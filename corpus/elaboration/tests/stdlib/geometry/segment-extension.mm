$( tests/stdlib/geometry/segment-extension, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A m $.
  $d B m $.
  $d C m $.
  tests.stdlib.geometry.segment-extension $p |- ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. RR ) /\ -. A = B ) /\ 0 < C ) -> E. m e. CC ( ( A =/= B /\ ( ( m - B ) / ( A - B ) ) e. RR /\ ( ( m - B ) / ( A - B ) ) < 0 ) /\ ( abs ` ( B - m ) ) = C ) ) $=
    ( cc wcel wa cr wceq wn cc0 clt wbr wne cv cmin co cdiv w3a cabs cfv wrex simpl id syl simpr jca neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid gextend ) AEFZBEFZGZCHFZGZABIZJZGZKCLMZGZVBABNZGZVFGVHDOZBPQZABPQZRQZHFVMKLMSBVJPQTUACIGDEUBVGVIVFVGVBVHVGUTVAVGURUSVGVEURVEVFUCZVEVBURVBVDUCZVBUTURUTVAUCZUTURURURUSUCURUDUEUEUEUEVGVEUSVNVEVBUSVOVBUTUSVPURUSUFUEUEUEUGVGVEVAVNVEVBVAVOUTVAUFUEUEUGVGBAIZJZVHVGABVGVEVDVNVBVDUFUEUHVGVHVRVGVHVDVRVHVDUIVGABUJUKVGVCVQVGVQVCVQVCUIVGBAULUKUMUNUOUMUPUGVEVFUFUGDABCUQUE $.
$}
