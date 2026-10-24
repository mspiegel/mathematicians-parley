$( tests/elaborator/a-congruence-read-either-way/a-congruence-claimed-the-other-way-round, elaborated from tests/elaborator/a-congruence-read-either-way.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]
$[ proofs/wiedijk/divisibility-by-three/congruent-times.mm $]

${
  tests.elaborator.a-congruence-read-either-way.a-congruence-claimed-the-other-way-round $p |- ( ( ( ( ( A e. ZZ /\ B e. ZZ ) /\ C e. ZZ ) /\ D e. NN ) /\ D || ( A - B ) ) -> D || ( ( B x. C ) - ( A x. C ) ) ) $=
    ( cz wcel wa cn cmin co cdvds wbr cmul simpl simpr syl id jca nnz gcongcomd bicomd mpbid proofs.wiedijk.divisibility-by-three.congruent-times ) AEFZBEFZGZCEFZGZDHFZGZDABIJZKLZGZUEUDGZUGGZUIGZDBAIJZKLZGDBCMJACMJIJKLUMUPURUMUOUIUMUNUGUMUEUDUMUJUEUJULNZUJUHUEUHUINZUHUFUEUFUGNZUDUEOZPZPZPZUMUJUDUSUJUHUDUTUHUFUDVAUFUDUDUDUENZUDQZPZPZPZPZRUMUJUGUSUJUHUGUTUFUGOPPRUMUJUIUSUHUIOZPZRUMULURUJULOUMURULUMBADUMUIDEFVMDSPVEVKTUAUBRBACDUCP $.
$}
