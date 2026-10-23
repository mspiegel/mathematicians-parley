$( tests/stdlib/calculus/continuous-on-a-part, elaborated from tests/stdlib/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.calculus.continuous-on-a-part $p |- ( ( ( A : RR --> RR /\ ( A |` RR ) e. ( RR -cn-> RR ) ) /\ B e. ~P RR ) -> ( A |` B ) e. ( B -cn-> RR ) ) $=
    ( cr wf cres ccncf co wcel wa cpw simpl id syl wss simpr elpwi gcncfpart ) CCADZACEZCCFGZHZIZBCJZHZIZCBAUEUBRUBUDKZUBRRRUAKRLMMUEUDBCNUBUDOBCPMUEUBUAUFRUAOMQ $.
$}
