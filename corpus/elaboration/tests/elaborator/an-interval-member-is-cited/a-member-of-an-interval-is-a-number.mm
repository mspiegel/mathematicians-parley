$( tests/elaborator/an-interval-member-is-cited/a-member-of-an-interval-is-a-number, elaborated from tests/elaborator/an-interval-member-is-cited.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A x $.
  $d B x $.
  tests.elaborator.an-interval-member-is-cited.a-member-of-an-interval-is-a-number $p |- ( ( A e. RR /\ B e. RR ) -> A. x e. ( A [,] B ) ( ( x x. 2 ) + A ) e. RR ) $=
    ( cr wcel wa cv c2 cmul co caddc cicc simpl id syl simpr geliccre syl3anc 2re a1i remulcld readdcld ralrimiva ) BDEZCDEZFZAGZHIJZBKJDEABCLJZUFUGUIEZFZUHBUKUGHUKUDUEUJUGDEUKUFUDUFUJMZUFUDUDUDUEMZUDNZOZOZUKUFUEULUDUEPOUFUJPBCUGQRHDEUKSTUAUPUBUC $.
$}
