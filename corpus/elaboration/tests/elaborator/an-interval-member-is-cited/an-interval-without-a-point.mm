$( tests/elaborator/an-interval-member-is-cited/an-interval-without-a-point, elaborated from tests/elaborator/an-interval-member-is-cited.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.elaborator.an-interval-member-is-cited.an-interval-without-a-point $p |- ( ( ( ( A e. RR /\ B e. RR ) /\ C e. RR ) /\ D e. ( ( A [,] B ) \ { C } ) ) -> 0 <_ ( D ^ 2 ) ) $=
    ( cr wcel wa cicc co csn cdif cc0 c2 cexp cle wbr simpl id syl simpr eldifi geliccre syl3anc sqge0 ) AEFZBEFZGZCEFZGZDABHIZCJZKZFZGZDEFZLDMNIOPUNUEUFDUJFZUOUNUIUEUIUMQZUIUGUEUGUHQZUGUEUEUEUFQUERSSSUNUIUFUQUIUGUFURUEUFTSSUNUMUPUIUMTDUJUKUASABDUBUCDUDS $.
$}
