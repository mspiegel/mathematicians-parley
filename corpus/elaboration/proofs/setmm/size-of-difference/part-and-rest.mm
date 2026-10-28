$( proofs/setmm/size-of-difference/part-and-rest, elaborated from proofs/setmm/size-of-difference.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/sets/subset-antisymmetric.mm $]

${
  $d A m $.
  $d B m $.
  proofs.setmm.size-of-difference.part-and-rest $p |- ( ( ( A e. _V /\ B e. _V ) /\ B C_ A ) -> ( B u. ( A \ B ) ) = A ) $=
    ( cvv wcel wa wss cdif cun wceq simpl simpr syl id difexg jca unexg difss a1i unss sylib vm cv wral wn elun1 wb eldif mpbird elun2 wo exmid mpjaodan ralrimiva dfss3 stdlib.sets.subset-antisymmetric ) ACDZBCDZEZBAFZEZBABGZHZCDZUPEZVBAFZEZAVBFZEVBAIUTVFVGUTVDVEUTVCUPUTUQVACDZEVCUTUQVHUTURUQURUSJZUPUQKLUTUPVHUTURUPVIURUPUPUPUQJZUPMZLZLZABCNLOBVACCPLVMOUTUSVAAFZEVEUTUSVNURUSKVNUTABQROBVAASTOUTVGUAUBZVBDZUAAUCZUTVPUAAUTVOADZEZVOBDZVPVTUDZVSVTEVTVPVSVTKVOBVAUELVSWAEZVOVADZVPWBWCVRWAEZWBVRWAWBVSVRVSWAJUTVRKLVSWAKOWCWDUFWBVOABUGRUHVOVABUILVTWAUJVSVTUKRULUMVGVQUFUTUAAVBUNRUHOVBAUOL $.
$}
