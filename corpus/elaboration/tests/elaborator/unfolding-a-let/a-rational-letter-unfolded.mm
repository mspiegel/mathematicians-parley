$( tests/elaborator/unfolding-a-let/a-rational-letter-unfolded, elaborated from tests/elaborator/unfolding-a-let.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d p q $.
  $d A p q $.
  tests.elaborator.unfolding-a-let.a-rational-letter-unfolded $p |- ( A e. QQ -> E. p e. ZZ E. q e. NN A = ( p / q ) ) $=
    ( cq wcel cv cdiv co wceq cn wrex cz id wb elq a1i mpbid ) ADEZRACFZBFZGHZIZBJKZCLKZRMRUDNRCBAOPQ $.
$}
