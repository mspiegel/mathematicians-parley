$( tests/elaborator/a-define-cited-as-a-step/a-define-cited-as-a-step, elaborated from tests/elaborator/a-define-cited-as-a-step.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d j k m x $.
  $d A j k m x $.
  $d B j k m x $.
  tests.elaborator.a-define-cited-as-a-step.a-define-cited-as-a-step $p |- ( ( A e. _V /\ B : A --> A ) -> ( x e. A |-> ( B ` x ) ) Fn A ) $=
    ( cvv wcel wf wa vk cv vm cfv cmpt wceq wex wfn simpl id syl mptexg elisset wral vj fvex a1i ralrimiva fveq2d eleq1d cbvralvw sylib eqid mptfng simpr fneq1d mpbird cbvmptv eqtrd mpbid ex exlimdv mpd ) BDEZBBCFZGZHIZJBJIZCKZLZMZHNZABAIZCKZLZBOZVCVGDEZVIVCVAVNVCVAVAVAVBPVAQRJBVFDSRHVGDTRVCVHVMHVCVHVMVCVHGZVDBOZVMVOVPVGBOZVOVFDEZJBUAZVQVOUBIZCKZDEZUBBUAVSVOWBUBBWBVOVTBEGVTCUCUDUEWBVRUBJBVTVEMZWAVFDWCVTVECWCQUFUGUHUIJBVFVGVGUJUKUIVOBVDVGVCVHULZUMUNVOBVDVLVOVDVGVLWDVGVLMVOJABVFVKVEVJMZVEVJCWEQUFUOUDUPUMUQURUSUT $.
$}
