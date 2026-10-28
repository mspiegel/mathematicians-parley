$( tests/stdlib/geometry/parallel, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d m u $.
  $d A m u $.
  $d B m u $.
  $d C m u $.
  $d D m u $.
  tests.stdlib.geometry.parallel $p |- ( ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. CC ) /\ -. A = B ) /\ -. C = D ) /\ ( ( B - A ) / ( D - C ) ) e. RR ) -> ( { u e. CC | ( A = B \/ ( ( u - A ) / ( B - A ) ) e. RR ) } = { u e. CC | ( C = D \/ ( ( u - C ) / ( D - C ) ) e. RR ) } \/ -. E. m e. CC ( ( A = B \/ ( ( m - A ) / ( B - A ) ) e. RR ) /\ ( C = D \/ ( ( m - C ) / ( D - C ) ) e. RR ) ) ) ) $=
    ( cc wcel wa wceq wn cmin co cdiv cr cv wo crab wrex simpr wne wb simpl id syl jca neqcomd df-ne a1i eqcom bicomd notbid bitrd mpbid gpardef ) BGHZCGHZIZDGHZIZEGHZIZBCJZKZIZDEJZKZIZCBLMZEDLMZNMZOHZIZVLVCAPZBLMZVINMZOHZQZAGRZVFVNDLMZVJNMZOHZQZAGRZJZVCFPZBLMZVINMZOHZQZVFWFDLMZVJNMZOHZQZIZFGSZKZQZVHVLTVMVBBCUAZIZDEUAZIVLWRUBVMWTXAVMVBWSVMUTVAVMURUSVMUPUQVMVHUPVHVLUCZVHVEUPVEVGUCZVEVBUPVBVDUCZVBUTUPUTVAUCZUTURUPURUSUCZURUPUPUPUQUCUPUDUEUEUEUEUEUEVMVHUQXBVHVEUQXCVEVBUQXDVBUTUQXEUTURUQXFUPUQTUEUEUEUEUEUFVMVHUSXBVHVEUSXCVEVBUSXDVBUTUSXEURUSTUEUEUEUEUFVMVHVAXBVHVEVAXCVEVBVAXDUTVATUEUEUEUFVMCBJZKZWSVMBCVMVHVDXBVHVEVDXCVBVDTUEUEUGVMWSXHVMWSVDXHWSVDUBVMBCUHUIVMVCXGVMXGVCXGVCUBVMCBUJUIUKULUMUKUNUFVMEDJZKZXAVMDEVMVHVGXBVEVGTUEUGVMXAXJVMXAVGXJXAVGUBVMDEUHUIVMVFXIVMXIVFXIVFUBVMEDUJUIUKULUMUKUNUFFABCDEUOUEUN $.
$}
