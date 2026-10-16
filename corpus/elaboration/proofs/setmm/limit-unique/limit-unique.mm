$( proofs/setmm/limit-unique/limit-unique, elaborated from proofs/setmm/limit-unique.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/setmm/limit-unique/limit-at-most.mm $]

${
  $d A n $.
  $d B n $.
  $d C n $.
  proofs.setmm.limit-unique.limit-unique $p |- ( ( ( ( ( A : NN --> RR /\ B e. RR ) /\ C e. RR ) /\ ( n e. NN |-> ( A ` n ) ) ~~> B ) /\ ( n e. NN |-> ( A ` n ) ) ~~> C ) -> B = C ) $=
    ( cn cr wf wcel wa cv cfv cmpt cli wbr wceq cle simpl id syl simpr jca proofs.setmm.limit-unique.limit-at-most wb letri3 syl2anc mpbird ) EFAGZBFHZIZCFHZIZDEDJZAKZLZBMNZIZUNCMNZIZBCOZBCPNZCBPNZIZURUTVAURURUTURUPUQURUKUOURUIUJURUGUHURUPUGUPUQQZUPUKUGUKUOQZUKUIUGUIUJQZUIUGUGUGUHQZUGRZSZSZSZSZURUPUHVCUPUKUHVDUKUIUHVEUGUHTZSZSZSZUAURUPUJVCUPUKUJVDUIUJTZSZSZUAURUPUOVCUKUOTZSZUAUPUQTZUAABCDUBSURUGUJIZUHIZUQIZUOIVAURWDUOURWCUQURWBUHURUGUJVKVRUAVOUAWAUAVTUAACBDUBSUAURUHUJUSVBUCVOVRBCUDUEUF $.
$}
