$( tests/stdlib/numbers/integer-step, elaborated from tests/stdlib/numbers.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  integers $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ A < B ) -> ( A + 1 ) <_ B ) $=
    ( cz wcel wa clt wbr c1 caddc co cle simpr wb simpl id syl jca zltp1le mpbid ) ACDZBCDZEZABFGZEZUCAHIJZBKGZUBUCLUDUBUCUFMUDTUAUDUBTUBUCNZUBTTTUANTOPPUDUBUAUGTUALPQABRPS $.
$}
