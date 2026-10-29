$( proofs/setmm/group-inverses/group-cancel-inverse, elaborated from proofs/setmm/group-inverses.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/setmm/group-inverses/group-left-identity.mm $]

${
  proofs.setmm.group-inverses.group-cancel-inverse $p |- ( ( ( A e. Grp /\ B e. ( Base ` A ) ) /\ C e. ( Base ` A ) ) -> ( B ( +g ` A ) ( ( ( invg ` A ) ` B ) ( +g ` A ) C ) ) = C ) $=
    ( cgrp wcel cbs cfv wa cminusg cplusg co c0g wceq w3a simpl id syl simpr jca eqid grpinvcl 3jca grpass wb eqcom a1i bicomd mpbid grprinv oveq1d eqtrd proofs.setmm.group-inverses.group-left-identity ) ADEZBAFGZEZHZCUNEZHZBBAIGZGZCAJGZKZVAKZALGZCVAKZCURVCBUTVAKZCVAKZVEURVGVCMZVCVGMZURUMUOUTUNEZUQNZHVHURUMVKURUPUMUPUQOZUPUMUMUMUOOZUMPZQZQZURUOVJUQURUPUOVLUMUORZQZURUPVJURUMUOVPVRSZUNAUSBUNTZUSTZUAQUPUQRZUBSUNVAABUTCVTVATZUCQURVIVHVIVHUDURVCVGUEUFUGUHURVFVDCVAURUPVFVDMVSUNVAAUSBVDVTWCVDTWAUIQUJUKURUMUQHVECMURUMUQVPWBSACULQUK $.
$}
