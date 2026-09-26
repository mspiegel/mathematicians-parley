$( tests/stdlib/sets/difference-self, elaborated from tests/stdlib/sets.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  differe1 $p |- ( A e. _V -> ( A \ A ) = (/) ) $=
    ( cdif c0 wceq cvv wcel difid a1i ) AABCDAEFAGH $.
$}
