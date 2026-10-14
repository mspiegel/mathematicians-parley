$( tests/elaborator/a-define-filling-a-cited-function/value-at-one, elaborated from tests/elaborator/a-define-filling-a-cited-function.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A k $.
  tests.elaborator.a-define-filling-a-cited-function.value-at-one $p |- ( ( A : NN --> RR /\ A. k e. NN ( A ` k ) = ( k + 1 ) ) -> ( A ` 1 ) = ( 1 + 1 ) ) $=
    ( cn cr wf cv cfv c1 caddc co wceq wral wa simpr wcel wi 1nn a1i id fveq2d oveq1d eqeq12d rspcv syl mpd ) CDAEZBFZAGZUGHIJZKZBCLZMZUKHAGZHHIJZKZUFUKNULHCOZUKUOPUPULQRUJUOBHCUGHKZUHUMUIUNUQUGHAUQSZTUQUGHHIURUAUBUCUDUE $.
$}
