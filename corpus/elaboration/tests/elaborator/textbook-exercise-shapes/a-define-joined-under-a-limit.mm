$( tests/elaborator/textbook-exercise-shapes/a-define-joined-under-a-limit, elaborated from tests/elaborator/textbook-exercise-shapes.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d i j k m n $.
  $d A i j k m n $.
  $d B i j k m n $.
  tests.elaborator.textbook-exercise-shapes.a-define-joined-under-a-limit $p |- ( ( ( A : NN --> RR /\ B e. RR ) /\ ( n e. NN |-> sum_ k e. ( 1 ... n ) ( A ` k ) ) ~~> B ) -> ( n e. NN |-> sum_ k e. ( 1 ... n ) ( A ` k ) ) ~~> B ) $=
    ( cn cr wf wcel wa c1 cv cfz co cfv csu cmpt cli wbr vi vj vm wceq wex cvv nnex a1i mptexg syl elisset simpl simpr ex exlimdv mpd ) EFAGZBFHZIZDEJDKZLMZCKZANZCOZPZBQRZIZSKZTEJTKZLMZUAKZANZUAOZPZUBZSUCZVDVEVLUDHZVNVEEUDHZVOVPVEUEUFTEVKUDUGUHSVLUDUIUHVEVMVDSVEVMVDVEVMIVEVDVEVMUJUQVDUKUHULUMUN $.
$}
