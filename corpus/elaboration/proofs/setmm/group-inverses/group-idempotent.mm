$( proofs/setmm/group-inverses/group-idempotent, elaborated from proofs/setmm/group-inverses.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  proofs.setmm.group-inverses.group-idempotent $p |- ( ( A e. Grp /\ B e. ( Base ` A ) ) -> ( ( B ( +g ` A ) B ) = B <-> B = ( 0g ` A ) ) ) $=
    ( cgrp wcel cbs cfv wa cplusg co wceq c0g simpr simpl eqid grprid syl eqcomd eqtrd w3a wb id grpidcl 3jca jca grplcan mpbid oveq2d impbida ) ACDZBAEFZDZGZBBAHFZIZBJZBAKFZJZULUOGZUNBUPUMIZJZUQURUNBUSULUOLURUSBURULUSBJZULUOMZUJUMABUPUJNZUMNZUPNZOZPQRURUIUKUPUJDZUKSZGUTUQTURUIVHURULUIVBULUIUIUIUKMZUIUAZPZPURUKVGUKURULUKVBUIUKLZPZURULVGVBULUIVGVKUJAUPVCVEUBPPVMUCUDUJUMABUPBVCVDUEPUFULUQGZUNUSBVNBUPBUMULUQLUGVNULVAULUQMVFPRUH $.
$}
