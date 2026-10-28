$( tests/stdlib/sets/replacement, elaborated from tests/stdlib/sets.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A x $.
  $d B x $.
  $d C x $.
  tests.stdlib.sets.replacement $p |- ( ( ( A e. _V /\ B e. _V ) /\ C : A --> B ) -> ran ( x e. A |-> ( C ` x ) ) e. _V ) $=
    ( cvv wcel wa wf cv cfv cmpt crn simpl id syl grnmptex ) BEFZCEFZGZBCDHZGZQABAIZDJZKLEFUASQSTMSQQQRMQNOOABUCEPO $.
$}
