$( tests/stdlib/calculus/a-map-continuous-on-a-part, elaborated from tests/stdlib/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A y $.
  $d B y $.
  $d C y $.
  tests.stdlib.calculus.a-map-continuous-on-a-part $p |- ( ( ( ( A e. ~P RR /\ B e. ~P A ) /\ C : A --> RR ) /\ ( C |` B ) e. ( B -cn-> RR ) ) -> ( ( y e. B |-> ( C ` y ) ) |` B ) e. ( B -cn-> RR ) ) $=
    ( cr cpw wcel wa wf cres ccncf co simpl simpr syl wss elpwi gcncfmappart ) BEFZGZCBFZGZHZBEDIZHZDCJZCEKLZGZHZABCDUIUEUDUEUHMZUCUDNOUIUBCBPUIUEUBUJUEUCUBUCUDMTUBNOOCBQOUEUHNR $.
$}
