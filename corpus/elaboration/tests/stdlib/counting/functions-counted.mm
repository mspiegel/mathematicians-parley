$( tests/stdlib/counting/functions-counted, elaborated from tests/stdlib/counting.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.counting.functions-counted $p |- ( ( ( ( A e. _V /\ B e. _V ) /\ A e. Fin ) /\ B e. Fin ) -> ( # ` ( B ^m A ) ) = ( ( # ` B ) ^ ( # ` A ) ) ) $=
    ( cvv wcel wa cfn simpl simpr syl gmapcnt ) ACDZBCDZEZAFDZEZBFDZEZABQONOPGMNHIOPHJ $.
$}
