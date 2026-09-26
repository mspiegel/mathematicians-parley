$( tests/stdlib/numbers/abs-product, elaborated from tests/stdlib/numbers.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  absprodu $p |- ( ( A e. RR /\ B e. RR ) -> ( abs ` ( A x. B ) ) = ( ( abs ` A ) x. ( abs ` B ) ) ) $=
    ( cr wcel wa cc cmul co cabs cfv wceq simpl id syl recn simpr jca absmul ) ACDZBCDZEZAFDZBFDZEABGHIJAIJBIJGHKUAUBUCUASUBUASSSTLSMNAONUATUCSTPBONQABRN $.
$}
