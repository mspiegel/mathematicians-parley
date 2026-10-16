$( proofs/setmm/group-inverses/group-left-identity, elaborated from proofs/setmm/group-inverses.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/setmm/group-inverses/group-left-inverse.mm $]

${
  proofs.setmm.group-inverses.group-left-identity $p |- ( ( A e. Grp /\ B e. ( Base ` A ) ) -> ( ( 0g ` A ) ( +g ` A ) B ) = B ) $=
    ( cgrp wcel cbs cfv wa c0g cplusg co cminusg eqid grprinv oveq1d eqcomd w3a wceq simpl id syl simpr grpinvcl 3jca jca grpass eqtrd proofs.setmm.group-inverses.group-left-inverse oveq2d grprid ) ACDZBAEFZDZGZAHFZBAIFZJZBUNUOJZBUMUPBBAKFZFZBUOJZUOJZUQUMUPBUSUOJZBUOJZVAUMVCUPUMVBUNBUOUKUOAURBUNUKLZUOLZUNLZURLZMNOUMUJULUSUKDZULPZGVCVAQUMUJVIUMUJUJUJULRZUJSZTZUMULVHULUJULUAZUKAURBVDVGUBVMUCUDUKUOABUSBVDVEUETUFUMUTUNBUOUMUMUTUNQUMUJULVLVMUDABUGTUHUFUKUOABUNVDVEVFUIUF $.
$}
