$( tests/stdlib/calculus/a-derivative-on-a-part-is-real, elaborated from tests/stdlib/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.calculus.a-derivative-on-a-part-is-real $p |- ( ( ( ( ( A e. ~P RR /\ B : A --> RR ) /\ C e. ~P A ) /\ C C_ dom ( RR _D B ) ) /\ D e. C ) -> ( ( RR _D B ) ` D ) e. RR ) $=
    ( cr cpw wcel wf wa cdv co cdm wss simpl id syl elpwi simpr gdvrepart ) AEFZGZAEBHZIZCAFZGZIZCEBJKZLZMZIZDCGZIZDACBULUAAEMULUJUAUJUKNZUJUFUAUFUINZUFUCUAUCUENZUCUAUAUAUBNUAOPPPPAEQPULUJUBUMUJUFUBUNUFUCUBUOUAUBRPPPULUJUIUMUFUIRPUJUKRS $.
$}
