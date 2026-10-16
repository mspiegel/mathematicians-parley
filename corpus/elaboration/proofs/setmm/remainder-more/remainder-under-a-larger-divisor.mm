$( proofs/setmm/remainder-more/remainder-under-a-larger-divisor, elaborated from proofs/setmm/remainder-more.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/setmm/remainder-real/remainder-is-real.mm $]
$[ proofs/setmm/remainder-bounds/remainder-nonnegative.mm $]
$[ proofs/setmm/remainder-bounds/remainder-below-divisor.mm $]
$[ proofs/setmm/remainder-facts/remainder-of-small.mm $]

${
  proofs.setmm.remainder-more.remainder-under-a-larger-divisor $p |- ( ( ( ( ( ( A e. RR /\ B e. RR ) /\ C e. RR ) /\ 0 < B ) /\ 0 < C ) /\ B <_ C ) -> ( ( A mod B ) mod C ) = ( A mod B ) ) $=
    ( cr wcel wa cc0 clt wbr cle cmo co wceq simpl id syl simpr jca proofs.setmm.remainder-real.remainder-is-real proofs.setmm.remainder-bounds.remainder-nonnegative proofs.setmm.remainder-bounds.remainder-below-divisor ltletrd proofs.setmm.remainder-facts.remainder-of-small ) ADEZBDEZFZCDEZFZGBHIZFZGCHIZFZBCJIZFZABKLZDEZUGFZUKFZGUOJIZFZUOCHIZFUOCKLUOMUNUTVAUNURUSUNUQUKUNUPUGUNUFUIFZUPUNUFUIUNUDUEUNULUDULUMNZULUJUDUJUKNZUJUHUDUHUINZUHUFUDUFUGNZUFUDUDUDUENZUDOZPZPZPZPZPZUNULUEVCULUJUEVDUJUHUEVEUHUFUEVFUDUEQZPZPZPZPZRZUNULUIVCULUJUIVDUHUIQZPZPZRZABSZPZUNULUGVCULUJUGVDUJUHUGVEUFUGQZPZPZPZRUNULUKVCUJUKQPRUNVBUSWCABTPRUNUOBCWEVRWIUNVBUOBHIWCABUAPULUMQUBRUOCUCP $.
$}
