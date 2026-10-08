$( tests/stdlib/graphs/walk, elaborated from tests/stdlib/graphs.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d i m z $.
  $d A i m z $.
  $d B i m z $.
  $d C i m z $.
  $d D i m z $.
  tests.stdlib.graphs.walk $p |- ( ( ( ( ( A e. UMGraph /\ B e. NN0 ) /\ C : ( 1 ... B ) --> dom ( iEdg ` A ) ) /\ D : ( 0 ... B ) --> ( Vtx ` A ) ) /\ A. i e. ( 1 ... B ) ( ( iEdg ` A ) ` ( C ` i ) ) = { ( D ` ( i - 1 ) ) , ( D ` i ) } ) -> A. z e. ( 1 ... B ) ( ( iEdg ` A ) ` ( C ` z ) ) = { ( D ` ( z - 1 ) ) , ( D ` z ) } ) $=
    ( cumgr wcel cn0 wa c1 cfz co ciedg cfv cdm wf cc0 cvtx cv cmin cpr wceq wral simpr wb vm id fveq2d oveq1d preq12d eqeq12d cbvralvw bitri a1i mpbid biid mpbird ) BGHZCIHZJZKCLMZBNOZPZDQZJZRCLMZBSOZEQZJZFTZDOZVCOZVKKUAMZEOZVKEOZUBZUCZFVBUDZJZATZDOZVCOZWAKUAMZEOZWAEOZUBZUCZAVBUDZWIVTVSWIVJVSUEVSWIUFVTVSUGTZDOZVCOZWJKUAMZEOZWJEOZUBZUCZUGVBUDWIVRWQFUGVBVKWJUCZVMWLVQWPWRVLWKVCWRVKWJDWRUHZUIUIWRVOWNVPWOWRVNWMEWRVKWJKUAWSUJUIWRVKWJEWSUIUKULUMWQWHUGAVBWJWAUCZWLWCWPWGWTWKWBVCWTWJWADWTUHZUIUIWTWNWEWOWFWTWMWDEWTWJWAKUAXAUJUIWTWJWAEXAUIUKULUMUNUOUPWIWIUFVTWIUQUOUR $.
$}
