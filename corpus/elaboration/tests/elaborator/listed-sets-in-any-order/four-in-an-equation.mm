$( tests/elaborator/listed-sets-in-any-order/four-in-an-equation, elaborated from tests/elaborator/listed-sets-in-any-order.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]
$[ stdlib/sets/subset-antisymmetric.mm $]

${
  tests.elaborator.listed-sets-in-any-order.four-in-an-equation $p |- ( ( ( ( ( ( ( A e. _V /\ B e. _V ) /\ C e. _V ) /\ D e. _V ) /\ E e. _V ) /\ ( { B , C , D } u. { E } ) C_ A ) /\ A C_ ( { B , C , D } u. { E } ) ) -> A = ( { E , C , B } u. { D } ) ) $=
    ( cvv wcel wa ctp csn cun wss wceq simpl id syl tpex a1i snex jca unexg simpr stdlib.sets.subset-antisymmetric eqcomd wb eqcom tpcoma tpcomb eqtrd uneq1d gtpsnswap eqeq2d bitrd mpbid ) AFGZBFGZHZCFGZHZDFGZHZEFGZHZBCDIZEJZKZALZHZAVFLZHZVFAMZAECBIZDJZKZMZVJAVFVJUOVFFGZHZVIHZVGHAVFMZVJVRVGVJVQVIVJUOVPVJVHUOVHVINZVHVCUOVCVGNVCVAUOVAVBNVAUSUOUSUTNUSUQUOUQURNUQUOUOUOUPNUOOPPPPPPVJVDFGZVEFGZHVPVJWAWBWAVJBCDQRWBVJESRTVDVEFFUAPTVHVIUBTVJVHVGVTVCVGUBPTAVFUCPUDVJVKVSVOVKVSUEVJVFAUFRVJVFVNAVJVNVFVJVNBCEIZVMKZVFVJVLWCVMVJVLCEBIZWCVLWEMVJECBUGRVJWECBEIZWCWEWFMVJCEBUHRWFWCMVJCBEUGRUIUIUJWDVFMVJBCEDUKRUIUDULUMUN $.
$}
