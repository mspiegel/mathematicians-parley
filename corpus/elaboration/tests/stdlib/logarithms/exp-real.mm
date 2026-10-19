$( tests/stdlib/logarithms/exp-real, elaborated from tests/stdlib/logarithms.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.logarithms.exp-real $p |- ( A e. RR -> ( exp ` A ) e. RR ) $=
    ( cr wcel ce cfv id reefcl syl ) ABCZIADEBCIFAGH $.
$}
