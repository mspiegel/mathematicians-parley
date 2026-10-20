$( tests/stdlib/calculus/a-convergent-bounded-on-both-sides, elaborated from tests/stdlib/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d i j k m n $.
  $d A i j k m n $.
  $d B i j k m n $.
  tests.stdlib.calculus.a-convergent-bounded-on-both-sides $p |- ( ( ( A : NN --> RR /\ B e. RR ) /\ ( n e. NN |-> ( A ` n ) ) ~~> B ) -> E. k e. RR A. m e. NN ( abs ` ( A ` m ) ) <_ k ) $=
    ( cn cr wf wcel wa cv cfv cmpt cli wbr vj simpl id syl simpr jca ffvelcdm wb vi wceq fveq2d cbvmptv breq1i bitri a1i mpbid gclimbddabs ) FGAHZBGIZJZEFEKZALZMZBNOZJZCBPKZALZDKZALZDPUTVCFIZJZUMVEJVDGIVFUMVEVFUTUMUTVEQUTUOUMUOUSQUOUMUMUMUNQUMRSSSUTVETUAFGVCAUBSUTUSPFVBMZBNOZUOUSTUSVHUCUTUSUDFUDKZALZMZBNOVHURVKBNEUDFUQVJUPVIUEZUPVIAVLRUFUGUHVKVGBNUDPFVJVBVIVAUEZVIVAAVMRUFUGUHUIUJUKVAVCUEZVAVCAVNRUFUL $.
$}
