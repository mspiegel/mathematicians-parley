$( tests/stdlib/divisibility/gcd-zero, elaborated from tests/stdlib/divisibility.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  gcdzero $p |- ( A e. NN0 -> ( A gcd 0 ) = A ) $=
    ( nn0gcdid0 ) AB $.
$}
