$( tests/stdlib/sets/intersection-commutes, elaborated from tests/stdlib/sets.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  intersec $p |- ( ( A e. _V /\ B e. _V ) -> ( A i^i B ) = ( B i^i A ) ) $=
    ( cin wceq cvv wcel wa incom a1i ) ABCBACDAEFBEFGABHI $.
$}
