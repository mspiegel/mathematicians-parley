$( tests/elaborator/reading-congruence/a-congruence-the-other-way-substituted-into, elaborated from tests/elaborator/reading-congruence.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.elaborator.reading-congruence.a-congruence-the-other-way-substituted-into $p |- ( ( ( ( ( ( A e. ZZ /\ B e. ZZ ) /\ C e. ZZ ) /\ D e. NN ) /\ D || ( B - A ) ) /\ A = C ) -> D || ( C - B ) ) $=
    ( cz wcel wa cn cmin co cdvds wbr wceq simpl simpr syl nnz id gcongcomd mpbid oveq1d breq2d ) AEFZBEFZGZCEFZGZDHFZGZDBAIJZKLZGZACMZGZDABIJZKLZDCBIJZKLUNUKUPUNULUKULUMNZUIUKOPUNBADUNUHDEFUNULUHURULUIUHUIUKNZUGUHOPPDQPUNULUDURULUIUDUSUIUGUDUGUHNZUGUEUDUEUFNZUCUDOPPPPUNULUCURULUIUCUSUIUGUCUTUGUEUCVAUEUCUCUCUDNUCRPPPPPSTUNUOUQDKUNACBIULUMOUAUBT $.
$}
