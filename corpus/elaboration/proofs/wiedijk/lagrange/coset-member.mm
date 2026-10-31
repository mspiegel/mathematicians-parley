$( proofs/wiedijk/lagrange/coset-member, elaborated from proofs/wiedijk/lagrange.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A m $.
  $d B m $.
  $d C m $.
  proofs.wiedijk.lagrange.coset-member $p |- ( ( ( A e. Grp /\ B e. ( SubGrp ` A ) ) /\ C e. ( Base ` A ) ) -> C e. ( { C } ( LSSum ` A ) B ) ) $=
    ( cgrp wcel csubg cfv wa cbs csn clsm co vm cv cplusg wceq wrex c0g simpl simpr syl eqid subg0cl id jca grprid eqcomd oveq2d eqeq2d rspcev wss w3a wb subgss 3jca gelcoset mpbird ) ADEZBAFGZEZHZCAIGZEZHZCCJZBAKGZLZEZCCMNZAOGZLZPZMBQZVDARGZBEZCCVNVJLZPZHVMVDVOVQVDUTVOVDVAUTVAVCSZURUTTZUAZBAVNVNUBZUCUAVDVPCVDURVCHVPCPVDURVCVDVAURVRVAURURURUTSZURUDZUAZUAZVAVCTZUEVBVJACVNVBUBZVJUBWAUFUAUGUEVLVQMVNBVIVNPZVKVPCWHVIVNCVJWHUDUHUIUJUAVDURBVBUKZVCULVHVMUMVDURWIVCWEVDUTWIVTVBBAWGUNUAWFUOMCBACUPUAUQ $.
$}
