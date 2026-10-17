$( proofs/setmm/group-cancellation/the-left-identity, elaborated from proofs/setmm/group-cancellation.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/setmm/group-cancellation/the-left-inverse.mm $]

${
  proofs.setmm.group-cancellation.the-left-identity $p |- ( ( A e. Grp /\ B e. ( Base ` A ) ) -> ( ( 0g ` A ) ( +g ` A ) B ) = B ) $=
    ( cgrp wcel cbs cfv wa c0g cplusg co cminusg wceq w3a simpl id syl simpr eqid grpinvcl 3jca jca grpass proofs.setmm.group-cancellation.the-left-inverse oveq2d eqeq2d mpbid grprinv oveq1d eqeq1d grprid eqtrd ) ACDZBAEFZDZGZAHFZBAIFZJZBUPUQJZBUOBBAKFZFZUQJZBUQJZUSLZURUSLUOVCBVABUQJZUQJZLZVDUOULUNVAUMDZUNMZGVGUOULVIUOULULULUNNZULOZPZUOUNVHUNULUNQZUMAUTBUMRZUTRZSVMTUAUMUQABVABVNUQRZUBPUOVFUSVCUOVEUPBUQUOUOVEUPLUOULUNVLVMUAABUCPUDUEUFUOVCURUSUOVBUPBUQUMUQAUTBUPVNVPUPRZVOUGUHUIUFUMUQABUPVNVPVQUJUK $.
$}
