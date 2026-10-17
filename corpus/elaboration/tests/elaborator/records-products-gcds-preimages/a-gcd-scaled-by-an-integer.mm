$( tests/elaborator/records-products-gcds-preimages/a-gcd-scaled-by-an-integer, elaborated from tests/elaborator/records-products-gcds-preimages.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.records-products-gcds-preimages.a-gcd-scaled-by-an-integer $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ C e. ZZ ) -> ( ( C x. A ) gcd ( C x. B ) ) = ( abs ` ( C x. ( A gcd B ) ) ) ) $=
    ( cz wcel wa w3a cmul co cgcd cabs cfv wceq simpr simpl id syl 3jca absmulgcd ) ADEZBDEZFZCDEZFZUCTUAGCAHICBHIJICABJIHIKLMUDUCTUAUBUCNUDUBTUBUCOZUBTTTUAOTPQQUDUBUAUETUANQRCABSQ $.
$}
