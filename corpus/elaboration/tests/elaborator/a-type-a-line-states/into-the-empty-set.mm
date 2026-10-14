$( tests/elaborator/a-type-a-line-states/into-the-empty-set, elaborated from tests/elaborator/a-type-a-line-states.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A t $.
  $d B t $.
  tests.elaborator.a-type-a-line-states.into-the-empty-set $p |- ( ( A e. _V /\ B : A --> (/) ) -> A. t e. A ( B ` t ) e. (/) ) $=
    ( cvv wcel c0 wf wa cv cfv simpl simpr syl jca ffvelcdm ralrimiva ) BDEZBFCGZHZAIZCJZFEZABSTBEZHZRUCHUBUDRUCUDSRSUCKQRLMSUCLNBFTCOMP $.
$}
