$( tests/stdlib/geometry/on-line-ends, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.on-line-ends $p |- ( ( A e. CC /\ B e. CC ) -> ( ( A = B \/ ( ( A - A ) / ( B - A ) ) e. RR ) /\ ( A = B \/ ( ( B - A ) / ( B - A ) ) e. RR ) ) ) $=
    ( cc wcel wa wceq cmin co cdiv cr wo gonends1 gonends2 jca ) ACDBCDEABFZAAGHBAGHZIHJDKOPPIHJDKABLABMN $.
$}
