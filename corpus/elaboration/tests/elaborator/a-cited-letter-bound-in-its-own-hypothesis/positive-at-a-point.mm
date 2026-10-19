$( tests/elaborator/a-cited-letter-bound-in-its-own-hypothesis/positive-at-a-point, elaborated from tests/elaborator/a-cited-letter-bound-in-its-own-hypothesis.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A n $.
  $d B n $.
  tests.elaborator.a-cited-letter-bound-in-its-own-hypothesis.positive-at-a-point $p |- ( ( ( A e. NN /\ B : NN --> RR ) /\ A. n e. NN 0 < ( B ` n ) ) -> 0 < ( B ` A ) ) $=
    ( cn wcel cr wf wa cc0 cv cfv clt wbr wral simpr wi simpl id syl wceq fveq2d breq2d rspcv mpd ) ADEZDFBGZHZICJZBKZLMZCDNZHZUKIABKZLMZUGUKOULUEUKUNPULUGUEUGUKQUGUEUEUEUFQUERSSUJUNCADUHATZUIUMILUOUHABUORUAUBUCSUD $.
$}
