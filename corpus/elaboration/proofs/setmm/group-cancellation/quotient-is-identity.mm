$( proofs/setmm/group-cancellation/quotient-is-identity, elaborated from proofs/setmm/group-cancellation.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/setmm/group-cancellation/quotient-times-divisor.mm $]
$[ proofs/setmm/group-cancellation/the-left-identity.mm $]

${
  proofs.setmm.group-cancellation.quotient-is-identity $p |- ( ( ( A e. Grp /\ B e. ( Base ` A ) ) /\ C e. ( Base ` A ) ) -> ( ( B ( +g ` A ) ( ( invg ` A ) ` C ) ) = ( 0g ` A ) <-> B = C ) ) $=
    ( cgrp wcel cbs cfv wa cminusg cplusg co c0g wceq simpl id syl simpr jca proofs.setmm.group-cancellation.quotient-times-divisor oveq1d eqeq1d mpbid eqcomd proofs.setmm.group-cancellation.the-left-identity eqtrd eqid grprinv impbida ) ADEZBAFGZEZHZCUJEZHZBCAIGZGZAJGZKZALGZMZBCMZUNUTHZBUSCUQKZCVBVCBVBURCUQKZBMZVCBMVBUNVEVBULUMVBUIUKVBUNUIUNUTNZUNULUIULUMNZULUIUIUIUKNZUIOZPZPZPZVBUNUKVFUNULUKVGUIUKQPPRVBUNUMVFULUMQZPZRABCSPVBVDVCBVBURUSCUQUNUTQTUAUBUCVBUIUMHZVCCMVBUIUMVLVNRACUDPUEUNVAHZURCUPUQKZUSVPBCUPUQUNVAQTVPVOVQUSMVPUIUMVPUNUIUNVANZVKPVPUNUMVRVMPRUJUQAUOCUSUJUFUQUFUSUFUOUFUGPUEUH $.
$}
