$( tests/elaborator/records-products-gcds-preimages/a-product-that-is-zero, elaborated from tests/elaborator/records-products-gcds-preimages.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.records-products-gcds-preimages.a-product-that-is-zero $p |- ( ( ( A e. RR /\ B e. RR ) /\ ( A x. B ) = 0 ) -> ( A = 0 \/ B = 0 ) ) $=
    ( cr wcel wa cmul co cc0 wceq wo simpr cc wb simpl id syl recn jca mul0or mpbid ) ACDZBCDZEZABFGZHIZEZUEAHIZBHIZJZUCUEKUFALDZBLDZEUEUIMUFUJUKUFUAUJUFUCUAUCUENZUCUAUAUAUBNUAOPPAQPUFUBUKUFUCUBULUAUBKPBQPRABSPT $.
$}
