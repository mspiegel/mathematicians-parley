$( proofs/setmm/inverse-of-value/inverse-of-value, elaborated from proofs/setmm/inverse-of-value.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  proofs.setmm.inverse-of-value.inverse-of-value $p |- ( ( ( ( ( A e. _V /\ B e. _V ) /\ ( C : A --> B /\ C : A -1-1-> B ) ) /\ ( C " A ) = B ) /\ D e. A ) -> ( `' C ` ( C ` D ) ) = D ) $=
    ( cvv wcel wa wf wf1 cima wceq cfv ccnv simpl simpr syl jca gf1cnvfv1 ) AEFZBEFZGZABCHZABCIZGZGZCAJZBKZGZDAFZGZUCUIGDCLCMLDKUJUCUIUJUDUCUJUHUDUHUINUHUEUDUEUGNUAUDOPPUBUCOPUHUIOQABDCRP $.
$}
