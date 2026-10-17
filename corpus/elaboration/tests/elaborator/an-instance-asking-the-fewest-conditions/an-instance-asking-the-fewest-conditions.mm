$( tests/elaborator/an-instance-asking-the-fewest-conditions/an-instance-asking-the-fewest-conditions, elaborated from tests/elaborator/an-instance-asking-the-fewest-conditions.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A x $.
  tests.elaborator.an-instance-asking-the-fewest-conditions.an-instance-asking-the-fewest-conditions $p |- ( ( ( A. x e. RR ( 0 < x -> ( x + 0 ) = x ) /\ A. x e. RR ( x + 0 ) = x ) /\ A e. RR ) -> ( A + 0 ) = A ) $=
    ( cc0 cv clt wbr caddc co wceq wi cr wral wa wcel simpl id syl simpr oveq1d eqeq12d rspcv mpd ) CADZEFZUCCGHZUCIZJZAKLZUFAKLZMZBKNZMZUIBCGHZBIZULUJUIULUJUJUJUKOUJPQUHUIRQULUKUIUNJUJUKRUFUNABKUCBIZUEUMUCBUOUCBCGUOPZSUPTUAQUB $.
$}
