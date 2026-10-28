$( tests/stdlib/sets/pairing, elaborated from tests/stdlib/sets.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.sets.pairing $p |- ( ( A e. _V /\ B e. _V ) -> { A , B } e. _V ) $=
    ( cpr cvv wcel wa prex a1i ) ABCDEADEBDEFABGH $.
$}
