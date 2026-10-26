$( tests/elaborator/a-conjunct-of-a-cited-line/a-condition-from-a-conjunct, elaborated from tests/elaborator/a-conjunct-of-a-cited-line.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A x $.
  $d B x $.
  $d C x $.
  $d D x $.
  $d E x $.
  tests.elaborator.a-conjunct-of-a-cited-line.a-condition-from-a-conjunct $p |- ( ( ( ( ( ( A e. RR /\ B e. RR ) /\ C e. ( A (,) B ) ) /\ D : ( A (,) B ) --> RR ) /\ A. x e. ( A (,) B ) ( -. x = C -> ( D ` x ) = 0 ) ) /\ E e. ( ( A (,) B ) \ { C } ) ) -> ( D ` E ) = 0 ) $=
    ( cr wcel wa cioo co wf cv wceq wn cfv cc0 wi wral csn cdif wne simpr eldifsn sylib wb df-ne a1i anbi2d mpbid syl simpl id eqeq1d notbid fveq2d imbi12d rspcv mpd ) BGHZCGHZIZDBCJKZHZIZVCGELZIZAMZDNZOZVHEPZQNZRZAVCSZIZFVCDTZUAZHZIZFDNZOZFEPZQNZVSFVCHZWAIZWAVSWDFDUBZIZWEVSVRWGVOVRUCZFVCDUDZUEZVSWFWAWDWFWAUFZVSFDUGZUHZUIZUJZWDWAUCUKVSVNWAWCRZVSVOVNVOVRULVGVNUCUKVSWDVNWPRVSWEWDWOWDWAULUKVMWPAFVCVHFNZVJWAVLWCWQVIVTWQVHFDWQUMZUNUOWQVKWBQWQVHFEWRUPUNUQURUKUSUS $.
$}
