$( tests/stdlib/sets/extensionality, elaborated from tests/stdlib/sets.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A x $.
  $d B x $.
  tests.stdlib.sets.extensionality $p |- ( ( ( ( A e. _V /\ B e. _V ) /\ A. x e. A x e. B ) /\ A. x e. B x e. A ) -> A = B ) $=
    ( cvv wcel wa cv wral wceq simpl simpr syl jca gext ) BDEZCDEZFZAGZCEZABHZFZRBEZACHZFZTUCFBCIUDTUCUDUATUAUCJQTKLUAUCKMABCNL $.
$}
