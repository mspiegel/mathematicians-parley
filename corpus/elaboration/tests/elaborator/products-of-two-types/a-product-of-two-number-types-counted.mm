$( tests/elaborator/products-of-two-types/a-product-of-two-number-types-counted, elaborated from tests/elaborator/products-of-two-types.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.products-of-two-types.a-product-of-two-number-types-counted $p |- ( ( ( ( A e. ~P ZZ /\ B e. ~P QQ ) /\ A e. Fin ) /\ B e. Fin ) -> ( # ` ( A X. B ) ) = ( ( # ` A ) x. ( # ` B ) ) ) $=
    ( cz cpw wcel cq wa cfn cxp chash cfv cmul co wceq simpl simpr syl jca hashxp ) ACDZEZBFDZEZGZAHEZGZBHEZGZUEUGGABIJKAJKBJKLMNUHUEUGUHUFUEUFUGOUDUEPQUFUGPRABSQ $.
$}
