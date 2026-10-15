$( proofs/setmm/square-roots-equal/square-roots-equal, elaborated from proofs/setmm/square-roots-equal.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  proofs.setmm.square-roots-equal.square-roots-equal $p |- ( ( ( ( A e. RR /\ B e. RR ) /\ 0 <_ A ) /\ 0 <_ B ) -> ( ( sqrt ` A ) = ( sqrt ` B ) <-> A = B ) ) $=
    ( cr wcel wa cc0 cle wbr csqrt cfv wceq c2 cexp co simpl id syl simpr jca resqrtth oveq1d eqeq1d mpbid eqcomd eqtrd fveq2d impbida ) ACDZBCDZEZFAGHZEZFBGHZEZAIJZBIJZKZABKZUNUQEZAUPLMNZBUSUTAUSUOLMNZAKZUTAKUSUNVBUNUQOZUNUHUKEVBUNUHUKUNULUHULUMOZULUJUHUJUKOZUJUHUHUHUIOUHPQQQUNULUKVDUJUKRQSATQQUSVAUTAUSUOUPLMUNUQRUAUBUCUDUSUNUTBKZVCUNUIUMEVFUNUIUMUNULUIVDULUJUIVEUHUIRQQULUMRSBTQQUEUNUREABIUNURRUFUG $.
$}
