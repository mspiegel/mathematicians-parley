$( proofs/hammack/ln-is-injective/ln-is-injective, elaborated from proofs/hammack/ln-is-injective.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  proofs.hammack.ln-is-injective.ln-is-injective $p |- ( ( ( ( ( A e. RR /\ B e. RR ) /\ 0 < A ) /\ 0 < B ) /\ ( log ` A ) = ( log ` B ) ) -> A = B ) $=
    ( cr wcel wa cc0 clt wbr clog cfv wceq ce crp simpl id syl simpr jca elrp sylibr reeflog eqcomd fveq2d eqtrd ) ACDZBCDZEZFAGHZEZFBGHZEZAIJZBIJZKZEZAUMLJZBUOAULLJZUPUOUQAUOAMDZUQAKUOUEUHEURUOUEUHUOUKUEUKUNNZUKUIUEUIUJNZUIUGUEUGUHNZUGUEUEUEUFNUEOPPPPUOUKUHUSUKUIUHUTUGUHQPPRASTAUAPUBUOULUMLUKUNQUCUDUOBMDZUPBKUOUFUJEVBUOUFUJUOUKUFUSUKUIUFUTUIUGUFVAUEUFQPPPUOUKUJUSUIUJQPRBSTBUAPUD $.
$}
