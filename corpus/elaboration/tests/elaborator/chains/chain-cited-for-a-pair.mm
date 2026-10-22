$( tests/elaborator/chains/chain-cited-for-a-pair, elaborated from tests/elaborator/chains.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.chains.chain-cited-for-a-pair $p |- ( ( ( ( ( ( ( A e. RR /\ B e. RR ) /\ C e. RR ) /\ D e. RR ) /\ ( ( A = B /\ B = C ) /\ C = D ) ) /\ ( A + 1 ) = 5 ) /\ ( D x. 2 ) = 6 ) -> ( ( D + 1 ) = 5 /\ ( A x. 2 ) = 6 ) ) $=
    ( cr wcel wa wceq c1 caddc co c5 c2 cmul c6 simpl simpr syl simpld simprd eqtrd oveq1d eqeq1d mpbid eqcomd jca ) AEFZBEFZGZCEFZGZDEFZGZABHZBCHZGZCDHZGZGZAIJKZLHZGZDMNKZOHZGZDIJKZLHZAMNKZOHZVEVAVGVEVBVAVBVDPZUSVAQRVEUTVFLVEADIJVEACDVEABCVEUNUOVEUPUQVEVBURVJVBUSURUSVAPZUMURQZRZRZSZSZVEUNUOVOTZUAZVEUPUQVNTZUAZUBUCUDVEVDVIVBVDQVEVCVHOVEDAMNVEADVTUEUBUCUDUF $.
$}
