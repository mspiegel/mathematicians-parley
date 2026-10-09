$( tests/stdlib/counting/one-to-one-counted, elaborated from tests/stdlib/counting.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d g j $.
  $d A g j $.
  $d B g j $.
  tests.stdlib.counting.one-to-one-counted $p |- ( ( ( ( ( A e. _V /\ B e. _V ) /\ A e. Fin ) /\ B e. Fin ) /\ ( # ` A ) <_ ( # ` B ) ) -> ( # ` { g e. ( B ^m A ) | g : A -1-1-> B } ) = prod_ j e. ( 0 ... ( ( # ` A ) - 1 ) ) ( ( # ` B ) - j ) ) $=
    ( cvv wcel wa cfn chash cfv cle wbr simpl simpr syl gf1cnt ) AEFZBEFZGZAHFZGZBHFZGZAIJZBIJZKLZGZCDABUGUCTUCUFMZUCUATUAUBMSTNOOUGUCUBUHUAUBNOUCUFNP $.
$}
