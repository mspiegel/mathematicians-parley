$( tests/stdlib/sets/replacement, elaborated from tests/stdlib/sets.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d m s x $.
  $d A m s x $.
  $d B m s x $.
  $d C m s x $.
  tests.stdlib.sets.replacement $p |- ( ( ( ( A e. _V /\ A e. _V ) /\ B e. _V ) /\ C : A --> B ) -> ran ( x e. A |-> ( C ` x ) ) e. _V ) $=
    ( cvv wcel wa wf vs cv cfv cmpt crn simpl simpr syl grnmptex wb vm wceq id fveq2d cbvmptv rneqi eleq1i bitri a1i mpbid ) BEFZUIGZCEFZGZBCDHZGZIBIJZDKZLZMZEFZABAJZDKZLZMZEFZUNUIUSUNULUIULUMNULUJUIUJUKNUIUIOPPIBUPEQPUSVDRUNUSSBSJZDKZLZMZEFVDURVHEUQVGISBUPVFUOVETZUOVEDVIUAUBUCUDUEVHVCEVGVBSABVFVAVEUTTZVEUTDVJUAUBUCUDUEUFUGUH $.
$}
