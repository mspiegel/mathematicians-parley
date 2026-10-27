$( tests/stdlib/geometry/triangle-off-line, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.triangle-off-line $p |- ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ -. B = C ) /\ -. ( B = C \/ ( ( A - B ) / ( C - B ) ) e. RR ) ) -> ( ( ( -. A = B /\ -. B = C ) /\ -. A = C ) /\ -. ( ( C - A ) / ( B - A ) ) e. RR ) ) $=
    ( cc wcel wa wceq wn cmin co cdiv cr wo wne simpl id syl simpr jca neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid gtrioff ) ADEZBDEZFZCDEZFZBCGZHZFZUOABIJZCBIJZKJZLEZMZHZFZUNBCNZFZVCFABGHUPFACGHFCAIJBAIJKJLEHFVDVFVCVDUNVEVDULUMVDUJUKVDUQUJUQVCOZUQUNUJUNUPOZUNULUJULUMOZULUJUJUJUKOUJPQQQQVDUQUKVGUQUNUKVHUNULUKVIUJUKRQQQSVDUQUMVGUQUNUMVHULUMRQQSVDCBGZHZVEVDBCVDUQUPVGUNUPRQTVDVEVKVDVEUPVKVEUPUAVDBCUBUCVDUOVJVDVJUOVJUOUAVDCBUDUCUEUFUGUEUHSUQVCRSABCUIQ $.
$}
