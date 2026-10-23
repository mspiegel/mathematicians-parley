$( tests/elaborator/textbook-exercise-shapes-two/a-limit-unfolded-on-the-line, elaborated from tests/elaborator/textbook-exercise-shapes-two.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d k m x $.
  $d A k m x $.
  $d B k m x $.
  $d C k m x $.
  tests.elaborator.textbook-exercise-shapes-two.a-limit-unfolded-on-the-line $p |- ( ( ( ( A : RR --> RR /\ B e. RR ) /\ C e. RR ) /\ C e. ( A limCC B ) ) -> A. m e. RR ( 0 < m -> E. k e. RR ( 0 < k /\ A. x e. RR ( ( -. x = B /\ ( abs ` ( x - B ) ) < k ) -> ( abs ` ( ( A ` x ) - C ) ) < m ) ) ) ) $=
    ( cr wf wcel wa climc co cc0 cv clt wbr wne cmin cabs cfv wi wral wrex wceq wn simpr wss ssid a1i simpl id syl glimcre mpbid wb df-ne anbi1d imbi1d ralbidva anbi2d rexbidva imbi2d ) GGBHZCGIZJZDGIZJZDBCKLZIZJZMFNZOPZMENZOPZANZCQZVOCRLZSTZVMOPZJZVOBTZDRLZSTZVKOPZUAZAGUBZJZEGUCZUAZFGUBZVLVNVOCUDZUEZVSJZWDUAZAGUBZJZEGUCZUAZFGUBVJVIWJVGVIUFVJFEAGCDBGGUGVJGUHUIVJVGVCVGVIUJZVGVEVCVEVFUJZVEVCVCVCVDUJVCUKULULULVJVGVDWSVGVEVDWTVCVDUFULULVJVGVFWSVEVFUFULUMUNVJWIWRFGVJVKGIZJZWHWQVLXBWGWPEGXBVMGIZJZWFWOVNXDWEWNAGXDVOGIZJZVTWMWDXFVPWLVSVPWLUOXFVOCUPUIUQURUSUTVAVBUSUN $.
$}
