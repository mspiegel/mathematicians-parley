$( tests/elaborator/reading-memberships/a-range-bound-substituted-into, elaborated from tests/elaborator/reading-memberships.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.reading-memberships.a-range-bound-substituted-into $p |- ( ( ( ( A e. ZZ /\ B e. ZZ ) /\ C e. ( 1 ... A ) ) /\ A = B ) -> C <_ B ) $=
    ( cz wcel wa c1 cfz co wceq cle wbr simpl simpr syl elfzle2 breq2d mpbid ) ADEZBDEZFZCGAHIZEZFZABJZFZCAKLZCBKLUFUCUGUFUDUCUDUEMUAUCNOCGAPOUFABCKUDUENQR $.
$}
