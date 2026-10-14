$( tests/stdlib/divisibility/mod-value, elaborated from tests/stdlib/divisibility.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.divisibility.mod-value $p |- ( ( ( A e. RR /\ B e. RR ) /\ 0 < B ) -> ( A mod B ) = ( A - ( B x. ( |_ ` ( A / B ) ) ) ) ) $=
    ( cr wcel wa cc0 clt wbr w3a cmo co cdiv cfl cfv cmul cmin wceq simpl id syl simpr 3jca gmodval ) ACDZBCDZEZFBGHZEZUDUEUGIABJKABABLKMNOKPKQUHUDUEUGUHUFUDUFUGRZUFUDUDUDUERUDSTTUHUFUEUIUDUEUATUFUGUAUBABUCT $.
$}
