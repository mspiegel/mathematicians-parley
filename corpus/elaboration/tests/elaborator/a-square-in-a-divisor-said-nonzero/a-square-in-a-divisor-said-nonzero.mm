$( tests/elaborator/a-square-in-a-divisor-said-nonzero/a-square-in-a-divisor-said-nonzero, elaborated from tests/elaborator/a-square-in-a-divisor-said-nonzero.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.a-square-in-a-divisor-said-nonzero.a-square-in-a-divisor-said-nonzero $p |- ( ( ( ( A e. RR /\ B e. RR ) /\ B = ( 1 / ( 1 + ( A ^ 2 ) ) ) ) /\ 0 <_ ( 1 / ( 1 + ( A ^ 2 ) ) ) ) -> 0 <_ B ) $=
    ( cr wcel wa c1 c2 cexp co caddc cdiv wceq cc0 cle wbr simpr simpl syl eqcomd breqtrd ) ACDZBCDZEZBFFAGHIZJIZKIZLZEZMUFNOZEZMUFBNUHUIPUJBUFUJUHUGUHUIQUCUGPRST $.
$}
