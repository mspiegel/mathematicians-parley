$( tests/stdlib/divisibility/mod-less, elaborated from tests/stdlib/divisibility.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  modless $p |- ( ( A e. ZZ /\ B e. NN ) -> ( A mod B ) < B ) $=
    ( gzmodlt ) ABC $.
$}
