$( tests/elaborator/a-congruence-read-either-way/a-congruence-cited-the-other-way-round, elaborated from tests/elaborator/a-congruence-read-either-way.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]
$[ proofs/wiedijk/divisibility-by-three/congruent-times.mm $]

${
  tests.elaborator.a-congruence-read-either-way.a-congruence-cited-the-other-way-round $p |- ( ( ( ( ( A e. ZZ /\ B e. ZZ ) /\ C e. ZZ ) /\ D e. NN ) /\ D || ( B - A ) ) -> D || ( ( A x. C ) - ( B x. C ) ) ) $=
    ( cz wcel wa cn cmin co cdvds wbr cmul simpl id syl simpr jca nnz gcongcomd mpbid proofs.wiedijk.divisibility-by-three.congruent-times ) AEFZBEFZGZCEFZGZDHFZGZDBAIJZKLZGZUIDABIJZKLZGDACMJBCMJIJKLULUIUNULUGUHULUEUFULUCUDULUIUCUIUKNZUIUGUCUGUHNZUGUEUCUEUFNZUEUCUCUCUDNZUCOZPZPZPZPZULUIUDUOUIUGUDUPUGUEUDUQUCUDQZPZPZPZRULUIUFUOUIUGUFUPUEUFQPPRULUIUHUOUGUHQZPZRULUKUNUIUKQULBADULUHDEFVIDSPVGVCTUARABCDUBP $.
$}
