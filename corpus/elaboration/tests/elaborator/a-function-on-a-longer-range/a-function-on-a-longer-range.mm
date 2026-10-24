$( tests/elaborator/a-function-on-a-longer-range/a-function-on-a-longer-range, elaborated from tests/elaborator/a-function-on-a-longer-range.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d i j k $.
  $d A i j k $.
  $d B i j k $.
  $d C i j k $.
  tests.elaborator.a-function-on-a-longer-range.a-function-on-a-longer-range $p |- ( ( ( ( A e. NN /\ B : ( 1 ... A ) --> RR ) /\ C e. NN ) /\ A. k e. ( 1 ... C ) ( B ` k ) e. RR ) -> prod_ k e. ( 1 ... C ) ( B ` k ) e. RR ) $=
    ( cn wcel c1 cfz co cr wf wa cv cfv wral vj cprod cfn fzfi a1i simpl simpr syl wi wceq id fveq2d eleq1d rspcv mpd fprodrecl wb vi cbvprodv eleq1i bitri mpbid ) AEFZGAHIZJBKZLZCEFZLZDMZBNZJFZDGCHIZOZLZVGPMZBNZPQZJFZVGVEDQZJFZVIVGVKPVGRFVIGCSTVIVJVGFZLZVHVKJFZVQVIVHVIVPUAVCVHUBUCVQVPVHVRUDVIVPUBVFVRDVJVGVDVJUEZVEVKJVSVDVJBVSUFUGUHUIUCUJUKVMVOULVIVMVGUMMZBNZUMQZJFVOVLWBJVGVKWAPUMVJVTUEZVJVTBWCUFUGUNUOWBVNJVGWAVEUMDVTVDUEZVTVDBWDUFUGUNUOUPTUQ $.
$}
