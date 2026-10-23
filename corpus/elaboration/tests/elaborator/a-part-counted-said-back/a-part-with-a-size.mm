$( tests/elaborator/a-part-counted-said-back/a-part-with-a-size, elaborated from tests/elaborator/a-part-counted-said-back.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A m $.
  tests.elaborator.a-part-counted-said-back.a-part-with-a-size $p |- ( ( A e. _V /\ E. m e. ~P A 1 <_ ( # ` m ) ) -> E. m e. ~P A 1 <_ ( # ` m ) ) $=
    ( cvv wcel c1 cv chash cfv cle wbr cpw wrex simpr ) ACDEBFGHIJBAKLM $.
$}
