$( proofs/setmm/group-inverses/group-inverse-by-right, elaborated from proofs/setmm/group-inverses.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  proofs.setmm.group-inverses.group-inverse-by-right $p |- ( ( ( A e. Grp /\ B e. ( Base ` A ) ) /\ C e. ( Base ` A ) ) -> ( ( ( invg ` A ) ` B ) = C <-> ( B ( +g ` A ) C ) = ( 0g ` A ) ) ) $=
    ( cgrp wcel cbs cfv wa cminusg wceq cplusg co c0g simpl id syl simpr jca eqid grprinv oveq2d eqeq1d mpbid eqcomd eqtrd w3a wb grpinvcl 3jca grplcan impbida ) ADEZBAFGZEZHZCUMEZHZBAIGZGZCJZBCAKGZLZAMGZJZUQUTHZBUSVALZVCJZVDVEUQVGUQUTNUQUOVGUQULUNUQUOULUOUPNZUOULULULUNNZULOZPZPZUQUOUNVHULUNQZPZRZUMVAAURBVCUMSZVASZVCSZURSZTZPZPVEVFVBVCVEUSCBVAUQUTQUAUBUCUQVDHZVFVBJZUTWBVFVCVBWBUQVGUQVDNZWAPWBVBVCUQVDQUDUEWBULUSUMEZUPUNUFZHWCUTUGWBULWFWBUQULWDVLPWBWEUPUNWBUQWEWDUQUOWEVOUMAURBVPVSUHPPWBUQUPWDUOUPQPWBUQUNWDVNPUIRUMVAAUSCBVPVQUJPUCUK $.
$}
