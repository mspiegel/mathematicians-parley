$( proofs/hammack/limit-unique/limit-unique, elaborated from proofs/hammack/limit-unique.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/hammack/limit-unique/limit-order.mm $]

${
  proofs.hammack.limit-unique.limit-unique $p |- ( ( ( ( ( ( A : RR --> RR /\ B e. RR ) /\ C e. RR ) /\ D e. RR ) /\ C e. ( A limCC B ) ) /\ D e. ( A limCC B ) ) -> C = D ) $=
    ( cr wf wcel wa climc co wceq cle wbr simpl id syl simpr jca proofs.hammack.limit-unique.limit-order wb letri3 syl2anc mpbird ) EEAFZBEGZHZCEGZHZDEGZHZCABIJZGZHZDUKGZHZCDKZCDLMZDCLMZHZUOUQURUOUFUIHZUGHZUNHZULHUQUOVBULUOVAUNUOUTUGUOUFUIUOUDUEUOUMUDUMUNNZUMUJUDUJULNZUJUHUDUHUINZUHUFUDUFUGNZUFUDUDUDUENZUDOZPZPZPZPZPZUOUMUEVCUMUJUEVDUJUHUEVEUHUFUEVFUDUEQZPZPZPZPZRZUOUMUIVCUMUJUIVDUHUIQZPZPZRUOUMUGVCUMUJUGVDUJUHUGVEUFUGQZPZPZPZRUMUNQZRUOUMULVCUJULQZPZRABDCSPUOUOURUOUMUNUOUJULUOUHUIUOUFUGVSWFRWBRWIRWGRABCDSPRUOUGUIUPUSTWFWBCDUAUBUC $.
$}
