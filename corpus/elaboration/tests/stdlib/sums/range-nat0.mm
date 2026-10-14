$( tests/stdlib/sums/range-nat0, elaborated from tests/stdlib/sums.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.sums.range-nat0 $p |- ( ( A e. ZZ /\ B e. ( 0 ... A ) ) -> B e. NN0 ) $=
    ( cz wcel cc0 cfz co wa cn0 simpr elfznn0 syl ) ACDZBEAFGZDZHOBIDMOJBAKL $.
$}
