$( tests/stdlib/sets/union-self, elaborated from tests/stdlib/sets.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  unionsel $p |- ( A e. _V -> ( A u. A ) = A ) $=
    ( cun wceq cvv wcel unidm a1i ) AABACADEAFG $.
$}
