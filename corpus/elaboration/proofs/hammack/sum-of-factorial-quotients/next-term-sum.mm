$( proofs/hammack/sum-of-factorial-quotients/next-term-sum, elaborated from proofs/hammack/sum-of-factorial-quotients.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d b j m $.
  $d A b j m $.
  $d B b j m $.
  proofs.hammack.sum-of-factorial-quotients.next-term-sum $p |- ( ( A e. NN /\ B : NN --> RR ) -> sum_ j e. ( 1 ... ( A + 1 ) ) ( B ` j ) = ( sum_ j e. ( 1 ... A ) ( B ` j ) + ( B ` ( A + 1 ) ) ) ) $=
    ( cn wcel cr wf wa c1 caddc co cfz vb cv cfv csu wceq cuz simpl id syl elnnuz sylib cc simpr elfznn ffvelcdm syl2anc recn fveq2d fsump1 wb vm cbvsumv eqeq1i oveq1i eqeq2i bitri a1i mpbid ) ADEZDFBGZHZIAIJKZLKZMNZBOZMPZIALKZVGMPZVDBOZJKZQZVECNZBOZCPZVIVOCPZVKJKZQZVCVGVKMIAVCVAAIROEVCVAVAVAVBSVATUAAUBUCVCVFVEEZHZVGFEZVGUDEWAVBVFDEZWBWAVCVBVCVTSVAVBUEUAWAVTWCVCVTUEVFVDUFUADFVFBUGUHVGUIUAVFVDQZVFVDBWDTUJUKVMVSULVCVMVEUMNZBOZUMPZVIWFUMPZVKJKZQZVSVMWGVLQWJVHWGVLVEVGWFMUMVFWEQZVFWEBWKTZUJZUNUOVLWIWGVJWHVKJVIVGWFMUMWMUNUPUQURWJVPWIQVSWGVPWIVEWFVOUMCWEVNQZWEVNBWNTZUJZUNUOWIVRVPWHVQVKJVIWFVOUMCWPUNUPUQURURUSUT $.
$}
