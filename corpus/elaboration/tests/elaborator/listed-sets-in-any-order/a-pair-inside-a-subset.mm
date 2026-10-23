$( tests/elaborator/listed-sets-in-any-order/a-pair-inside-a-subset, elaborated from tests/elaborator/listed-sets-in-any-order.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.listed-sets-in-any-order.a-pair-inside-a-subset $p |- ( ( ( A e. _V /\ B e. A ) /\ C e. A ) -> { C , B } C_ A ) $=
    ( cvv wcel wa cpr wss simpr simpl syl jca prssi ) ADEZBAEZFZCAEZFZQOFCBGAHRQOPQIRPOPQJNOIKLCBAMK $.
$}
