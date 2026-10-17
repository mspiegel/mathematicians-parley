$( proofs/hammack/gcd-with-remainder/gcd-with-remainder, elaborated from proofs/hammack/gcd-with-remainder.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  proofs.hammack.gcd-with-remainder.gcd-with-remainder $p |- ( ( ( ( ( A e. ZZ /\ B e. NN ) /\ C e. ZZ ) /\ D e. ZZ ) /\ A = ( ( C x. B ) + D ) ) -> ( A gcd B ) = ( D gcd B ) ) $=
    ( cz wcel cn wa cmul co caddc wceq cgcd cmo simpl id syl simpr jca modgcd eqcomd oveq1d w3a 3jca gmuladdmod eqtrd ) AEFZBGFZHZCEFZHZDEFZHZACBIJZDKJZLZHZABMJZDBNJZBMJZDBMJZUQURABNJZBMJZUTUQVCURUQUIVCURLUQUGUHUQUMUGUMUPOZUMUKUGUKULOZUKUIUGUIUJOZUIUGUGUGUHOUGPQQQQUQUMUHVDUMUKUHVEUKUIUHVFUGUHRZQZQZQZSABTQUAUQVBUSBMUQVBUOBNJZUSUQAUOBNUMUPRUBUQULUHUJUCVKUSLUQULUHUJUQUMULVDUKULRZQZVJUQUMUJVDUMUKUJVEUIUJRQQUDDBCUEQUFUBUFUQULUHHUTVALUQULUHVMVJSDBTQUF $.
$}
