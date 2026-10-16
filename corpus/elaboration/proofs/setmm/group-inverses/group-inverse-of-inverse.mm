$( proofs/setmm/group-inverses/group-inverse-of-inverse, elaborated from proofs/setmm/group-inverses.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/setmm/group-inverses/group-left-inverse.mm $]

${
  proofs.setmm.group-inverses.group-inverse-of-inverse $p |- ( ( A e. Grp /\ B e. ( Base ` A ) ) -> ( ( invg ` A ) ` ( ( invg ` A ) ` B ) ) = B ) $=
    ( cgrp wcel cbs cfv wa cminusg cplusg co wceq c0g simpl id syl eqid grpinvcl jca grprinv simpr proofs.setmm.group-inverses.group-left-inverse eqcomd eqtrd w3a wb 3jca grplcan mpbid ) ACDZBAEFZDZGZBAHFZFZUNUMFZAIFZJZUNBUPJZKZUOBKZULUQALFZURULUIUNUJDZGZUQVAKULUIVBULUIUIUIUKMZUINZOZUJAUMBUJPZUMPZQZRZUJUPAUMUNVAVGUPPZVAPVHSOULURVAULULURVAKULUIUKVFUIUKTZRABUAOUBUCULUIUOUJDZUKVBUDZGUSUTUEULUIVNVFULVMUKVBULVCVMVJUJAUMUNVGVHQOVLVIUFRUJUPAUOBUNVGVKUGOUH $.
$}
