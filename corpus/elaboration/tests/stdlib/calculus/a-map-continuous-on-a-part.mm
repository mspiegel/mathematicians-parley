$( tests/stdlib/calculus/a-map-continuous-on-a-part, elaborated from tests/stdlib/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d m x y $.
  $d A m x y $.
  $d B m x y $.
  $d C m x y $.
  tests.stdlib.calculus.a-map-continuous-on-a-part $p |- ( ( ( ( A e. ~P RR /\ B e. ~P A ) /\ C : A --> RR ) /\ ( C |` B ) e. ( B -cn-> RR ) ) -> ( ( y e. B |-> ( C ` y ) ) |` B ) e. ( B -cn-> RR ) ) $=
    ( cr cpw wcel wa wf cres ccncf co vx cv cfv cmpt simpl simpr syl wss elpwi gcncfmappart wb vm wceq id fveq2d cbvmptv reseq1i eleq1i bitri a1i mpbid ) BEFZGZCBFZGZHZBEDIZHZDCJZCEKLZGZHZMCMNZDOZPZCJZVBGZACANZDOZPZCJZVBGZVDMBCDVDUTUSUTVCQZURUSRSVDUQCBTVDUTUQVOUTURUQURUSQUOUQRSSCBUASUTVCRUBVIVNUCVDVIUDCUDNZDOZPZCJZVBGVNVHVSVBVGVRCMUDCVFVQVEVPUEZVEVPDVTUFUGUHUIUJVSVMVBVRVLCUDACVQVKVPVJUEZVPVJDWAUFUGUHUIUJUKULUM $.
$}
