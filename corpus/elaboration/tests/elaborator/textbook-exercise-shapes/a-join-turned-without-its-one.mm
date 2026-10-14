$( tests/elaborator/textbook-exercise-shapes/a-join-turned-without-its-one, elaborated from tests/elaborator/textbook-exercise-shapes.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.textbook-exercise-shapes.a-join-turned-without-its-one $p |- ( ( ( A e. RR /\ B e. RR ) /\ ( A x. 1 ) = B ) -> B = A ) $=
    ( cr wcel wa c1 cmul co wceq simpr cc simpl id syl recn mulrid eqeq1d mpbid eqcomd ) ACDZBCDZEZAFGHZBIZEZABUEUDABIUBUDJUEUCABUEAKDZUCAIUETUFUEUBTUBUDLUBTTTUALTMNNAONAPNQRS $.
$}
