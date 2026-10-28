$( tests/elaborator/listed-sets-in-any-order/a-triple-in-an-equation, elaborated from tests/elaborator/listed-sets-in-any-order.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/sets/subset-antisymmetric.mm $]

${
  tests.elaborator.listed-sets-in-any-order.a-triple-in-an-equation $p |- ( ( ( ( ( ( A e. _V /\ B e. _V ) /\ C e. _V ) /\ D e. _V ) /\ { B , C , D } C_ A ) /\ A C_ { B , C , D } ) -> { C , D , B } = A ) $=
    ( cvv wcel wa ctp wss wceq tpex a1i simpl id syl jca simpr stdlib.sets.subset-antisymmetric eqcomd wb eqcom tpcomb tpcoma eqtrd eqeq2d bitrd bicomd mpbid ) AEFZBEFZGZCEFZGZDEFZGZBCDHZAIZGZAUPIZGZAUPJZCDBHZAJZUTUPAUTUPEFZUIGZUQGZUSGUPAJUTVFUSUTVEUQUTVDUIVDUTBCDKLUTURUIURUSMZURUOUIUOUQMUOUMUIUMUNMUMUKUIUKULMUKUIUIUIUJMUINOOOOOPUTURUQVGUOUQQOPURUSQPUPAROSUTVCVAUTVCAVBJZVAVCVHTUTVBAUALUTVBUPAUTVBCBDHZUPVBVIJUTCDBUBLVIUPJUTCBDUCLUDUEUFUGUH $.
$}
