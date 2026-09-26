$( tests/stdlib/sums/range-nat, elaborated from tests/stdlib/sums.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  rangenat $p |- ( ( A e. ZZ /\ B e. ( 1 ... A ) ) -> B e. NN ) $=
    ( cz wcel c1 cfz co wa cn simpr elfznn syl ) ACDZBEAFGZDZHOBIDMOJBAKL $.
$}
