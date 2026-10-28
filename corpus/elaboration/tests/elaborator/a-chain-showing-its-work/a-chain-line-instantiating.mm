$( tests/elaborator/a-chain-showing-its-work/a-chain-line-instantiating, elaborated from tests/elaborator/a-chain-showing-its-work.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A x $.
  tests.elaborator.a-chain-showing-its-work.a-chain-line-instantiating $p |- ( ( A : RR --> RR /\ A. x e. RR ( A ` x ) = ( x + 1 ) ) -> ( A ` 2 ) = 3 ) $=
    ( cr wf cv cfv c1 caddc co wceq wral wa c2 c3 simpr wcel wi 2re a1i id fveq2d oveq1d eqeq12d rspcv syl mpd eqid oveq12i 2p1e3 eqtri eqtr4i eqtrd ) CCBDZAEZBFZUNGHIZJZACKZLZMBFZMGHIZNUSURUTVAJZUMUROUSMCPZURVBQVCUSRSUQVBAMCUNMJZUOUTUPVAVDUNMBVDTZUAVDUNMGHVEUBUCUDUEUFVANJUSVANNVAVANMMGGHMUGGUGUHUIUJNUGUKSUL $.
$}
