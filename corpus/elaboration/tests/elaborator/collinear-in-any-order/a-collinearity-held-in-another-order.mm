$( tests/elaborator/collinear-in-any-order/a-collinearity-held-in-another-order, elaborated from tests/elaborator/collinear-in-any-order.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.elaborator.collinear-in-any-order.a-collinearity-held-in-another-order $p |- ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ ( C = A \/ ( ( B - C ) / ( A - C ) ) e. RR ) ) -> ( B = C \/ ( ( A - B ) / ( C - B ) ) e. RR ) ) $=
    ( cc wcel wa wceq cmin co cdiv cr wo simpr w3a wi simpl syl id 3jca gcolrotate mpd wb biid a1i mpbird ) ADEZBDEZFZCDEZFZCAGZBCHIZACHIZJIZKEZLZFZBCGZABHIZCBHIZJIZKEZLZVCUQABGZCAHIZBAHIZJIZKEZLZVCUQUPVIUJUPMUQUIUFUGNUPVIOUQUIUFUGUQUJUIUJUPPZUHUIMZQZUQUJUFVJUJUHUFUHUIPZUHUFUFUFUGPZUFRZQZQZQZUQUJUGVJUJUHUGVMUFUGMZQZQZSCABTQUAUQUFUGUINVIVCOUQUFUGUIVRWAVLSABCTQUAVCVCUBUQVCUCUDUE $.
$}
