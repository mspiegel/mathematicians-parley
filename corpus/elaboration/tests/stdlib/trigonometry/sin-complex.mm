$( tests/stdlib/trigonometry/sin-complex, elaborated from tests/stdlib/trigonometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.trigonometry.sin-complex $p |- ( A e. CC -> ( sin ` A ) e. CC ) $=
    ( cc wcel csin cfv id sincl syl ) ABCZIADEBCIFAGH $.
$}
