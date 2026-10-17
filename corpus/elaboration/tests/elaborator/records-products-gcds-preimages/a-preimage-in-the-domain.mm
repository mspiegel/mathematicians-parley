$( tests/elaborator/records-products-gcds-preimages/a-preimage-in-the-domain, elaborated from tests/elaborator/records-products-gcds-preimages.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.elaborator.records-products-gcds-preimages.a-preimage-in-the-domain $p |- ( ( A : RR --> RR /\ B e. ~P RR ) -> ( `' A " B ) C_ RR ) $=
    ( cr wf cpw wcel wa ccnv cima wss simpl id syl gpreimass ) CCADZBCEZFZGZOAHBICJROOOQKOLMCCBANM $.
$}
