$( proofs/setmm/group-cancellation/element-of-its-coset, elaborated from proofs/setmm/group-cancellation.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A k $.
  $d B k $.
  $d C k $.
  $d D k $.
  proofs.setmm.group-cancellation.element-of-its-coset $p |- ( ( ( ( A e. Grp /\ B e. ( SubGrp ` A ) ) /\ C e. ( Base ` A ) ) /\ D e. B ) -> ( C ( +g ` A ) D ) e. ( { C } ( LSSum ` A ) B ) ) $=
    ( cgrp wcel csubg cfv wa cbs cplusg co csn clsm vk cv wceq wrex simpr eqidd jca id oveq2d eqeq2d rspcev syl wss w3a wb simpl eqid subgss 3jca gelcoset mpbird ) AEFZBAGHZFZIZCAJHZFZIZDBFZIZCDAKHZLZCMZBANHZLZFZVFCOPZVELZQZOBRZVDVCVFVFQZIVNVDVCVOVBVCSVDVFTUAVMVOODBVKDQZVLVFVFVPVKDCVEVPUBUCUDUEUFVDUPBUTUGZVAUHVJVNUIVDUPVQVAVDVBUPVBVCUJZVBUSUPUSVAUJZUSUPUPUPURUJUPUBUFUFUFVDURVQVDVBURVRVBUSURVSUPURSUFUFUTBAUTUKULUFVDVBVAVRUSVASUFUMOCBAVFUNUFUO $.
$}
