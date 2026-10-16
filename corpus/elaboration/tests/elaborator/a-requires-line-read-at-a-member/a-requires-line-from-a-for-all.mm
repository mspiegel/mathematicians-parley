$( tests/elaborator/a-requires-line-read-at-a-member/a-requires-line-from-a-for-all, elaborated from tests/elaborator/a-requires-line-read-at-a-member.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A m $.
  tests.elaborator.a-requires-line-read-at-a-member.a-requires-line-from-a-for-all $p |- ( ( A e. NN /\ A. m e. NN 0 < ( 2 ^ m ) ) -> 0 < ( 1 / ( 2 ^ A ) ) ) $=
    ( cn wcel cc0 c2 cv cexp co clt wbr wral wa cr c1 cdiv 2re a1i cn0 simpl id syl nnnn0 reexpcld simpr wi wceq oveq2d breq2d rspcv mpd jca recgt0 ) ACDZEFBGZHIZJKZBCLZMZFAHIZNDZEUTJKZMEOUTPIJKUSVAVBUSFAFNDUSQRUSUNASDUSUNUNUNURTZUNUAZUBZAUCUBUDUSURVBUNURUEUSUNURVBUFVEUQVBBACUOAUGZUPUTEJVFUOAFHVFUAUHUIUJUBUKULUTUMUB $.
$}
