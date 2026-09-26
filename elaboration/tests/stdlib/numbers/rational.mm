$( tests/stdlib/numbers/rational, elaborated from tests/stdlib/numbers.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d p q $.
  $d A p q $.
  rational $p |- ( ( A e. RR /\ A e. QQ ) -> E. p e. ZZ E. q e. NN A = ( p / q ) ) $=
    ( cr wcel cq wa cv cdiv co wceq cn wrex cz simpr wb elq a1i mpbid ) ADEZAFEZGZUAACHZBHZIJZKZBLMZCNMZTUAOUAUHPUBCBAQRS $.
$}
