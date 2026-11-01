$( tests/elaborator/identity-left-out/an-obtain-without-its-zero, elaborated from tests/elaborator/identity-left-out.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d k m q $.
  $d A k m q $.
  $d B k m q $.
  tests.elaborator.identity-left-out.an-obtain-without-its-zero $p |- ( ( ( A e. ZZ /\ B e. NN ) /\ E. q e. ZZ ( ( q x. B ) + 0 ) = A ) -> E. k e. ZZ ( k x. B ) = A ) $=
    ( cz wcel cn wa cv cmul co cc0 caddc wceq wrex vm simpr wb id oveq1d eqeq1d cbvrexvw a1i mpbid simpl syl cc zcn nncn mulcld addrid jca rspcev ex rexlimdva mpd ) AEFZBGFZHZDIZBJKZLMKZANZDEOZHZPIZBJKZLMKZANZPEOZCIZBJKZANZCEOZVEVDVJUSVDQVDVJRVEVCVIDPEUTVFNZVBVHAVOVAVGLMVOUTVFBJVOSTTUAUBUCUDVEVIVNPEVEVFEFZHZVIVNVQVIHZVPVGANZHVNVRVPVSVRVQVPVQVIUEZVEVPQZUFZVRVIVSVQVIQVRVHVGAVRVGUGFVHVGNVRVFBVRVPVFUGFWBVFUHUFVRURBUGFVRVQURVTVQVEURVEVPUEVEUSURUSVDUEUQURQUFUFUFBUIUFUJVGUKUFUAUDULVMVSCVFEVKVFNZVLVGAWCVKVFBJWCSTUAUMUFUNUOUP $.
$}
