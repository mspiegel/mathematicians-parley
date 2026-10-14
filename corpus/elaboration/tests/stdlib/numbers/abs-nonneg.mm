$( tests/stdlib/numbers/abs-nonneg, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.abs-nonneg $p |- ( A e. RR -> 0 <_ ( abs ` A ) ) $=
    ( cr wcel cc cc0 cabs cfv cle wbr id recn syl absge0 ) ABCZADCZEAFGHINNONJAKLAML $.
$}
