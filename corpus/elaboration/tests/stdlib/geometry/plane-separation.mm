$( tests/stdlib/geometry/plane-separation, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.plane-separation $p |- ( ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. CC ) /\ -. A = B ) /\ -. ( A = B \/ ( ( C - A ) / ( B - A ) ) e. RR ) ) /\ -. ( A = B \/ ( ( D - A ) / ( B - A ) ) e. RR ) ) -> ( 0 < ( ( Im ` ( ( C - A ) / ( B - A ) ) ) x. ( Im ` ( ( D - A ) / ( B - A ) ) ) ) \/ ( ( Im ` ( ( C - A ) / ( B - A ) ) ) x. ( Im ` ( ( D - A ) / ( B - A ) ) ) ) < 0 ) ) $=
    ( cc wcel wa wceq wn cmin co cdiv cr wo wne cc0 cim cfv cmul clt wbr simpl id syl simpr jca neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid gplanesep ) AEFZBEFZGZCEFZGZDEFZGZABHZIZGZVDCAJKZBAJKZLKZMFZNZIZGZVDDAJKZVHLKZMFZNZIZGZVCABOZGZVLGZVRGPVIQRZVOQRZSKZTUAWEPTUANVSWBVRVSWAVLVSVCVTVSVAVBVSUSUTVSUQURVSVMUQVMVRUBZVMVFUQVFVLUBZVFVCUQVCVEUBZVCVAUQVAVBUBZVAUSUQUSUTUBZUSUQUQUQURUBUQUCUDUDUDUDUDUDVSVMURWFVMVFURWGVFVCURWHVCVAURWIVAUSURWJUQURUEUDUDUDUDUDUFVSVMUTWFVMVFUTWGVFVCUTWHVCVAUTWIUSUTUEUDUDUDUDUFVSVMVBWFVMVFVBWGVFVCVBWHVAVBUEUDUDUDUFVSBAHZIZVTVSABVSVMVEWFVMVFVEWGVCVEUEUDUDUGVSVTWLVSVTVEWLVTVEUHVSABUIUJVSVDWKVSWKVDWKVDUHVSBAUKUJULUMUNULUOUFVSVMVLWFVFVLUEUDUFVMVRUEUFABCDUPUD $.
$}
