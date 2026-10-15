$( proofs/setmm/common-divisor-at-most-gcd/common-divisor-at-most-gcd, elaborated from proofs/setmm/common-divisor-at-most-gcd.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  proofs.setmm.common-divisor-at-most-gcd.common-divisor-at-most-gcd $p |- ( ( ( ( ( A e. NN /\ B e. NN ) /\ C e. NN ) /\ A || B ) /\ A || C ) -> A <_ ( B gcd C ) ) $=
    ( cn wcel wa cdvds wbr cgcd co cle simpl simpr syl jca cz w3a wi id nnz 3jca dvdsgcd mpd gcdnncl dvdsle ) ADEZBDEZFZCDEZFZABGHZFZACGHZFZABCIJZGHZAUOKHZUNUKUMFZUPUNUKUMUNULUKULUMLZUJUKMNULUMMOUNAPEZBPEZCPEZQURUPRUNUTVAVBUNUFUTUNULUFUSULUJUFUJUKLZUJUHUFUHUILZUHUFUFUFUGLZUFSZNZNZNZNZATZNZUNUGVAUNULUGUSULUJUGVCUJUHUGVDUFUGMZNZNZNZBTNUNUIVBUNULUIUSULUJUIVCUHUIMZNZNZCTNUAABCUBNUCUNUTUODEZFUPUQRUNUTVTVLUNUGUIFVTUNUGUIVPVSOBCUDNOAUOUENUC $.
$}
