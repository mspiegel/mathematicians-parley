$( tests/stdlib/geometry/congruent-by-symbol, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.geometry.congruent-by-symbol $p |- ( ( ( ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. CC ) /\ E e. CC ) /\ F e. CC ) /\ ( ( ( ( ( ( abs ` ( A - B ) ) = ( abs ` ( D - E ) ) /\ ( abs ` ( B - C ) ) = ( abs ` ( E - F ) ) ) /\ ( abs ` ( C - A ) ) = ( abs ` ( F - D ) ) ) /\ ( abs ` ( ( A - B ) ang ( C - B ) ) ) = ( abs ` ( ( D - E ) ang ( F - E ) ) ) ) /\ ( abs ` ( ( B - C ) ang ( A - C ) ) ) = ( abs ` ( ( E - F ) ang ( D - F ) ) ) ) /\ ( abs ` ( ( C - A ) ang ( B - A ) ) ) = ( abs ` ( ( F - D ) ang ( E - D ) ) ) ) ) /\ ( ( ( -. A = B /\ -. B = C ) /\ -. A = C ) /\ -. ( ( C - A ) / ( B - A ) ) e. RR ) ) /\ ( ( ( -. D = E /\ -. E = F ) /\ -. D = F ) /\ -. ( ( F - D ) / ( E - D ) ) e. RR ) ) -> ( abs ` ( A - B ) ) = ( abs ` ( D - E ) ) ) $=
    ( cc wcel wa cmin co cabs cfv wceq cang wn cdiv cr simpl simpr syl wb biid a1i mpbid ) AGHZBGHZIZCGHZIZDGHZIZEGHZIZFGHZIZABJKZLMZDEJKZLMZNZBCJKZLMZEFJKZLMZNZIZCAJKZLMZFDJKZLMZNZIZUQCBJKZOKZLMZUSFEJKZOKZLMZNZIZVBACJKZOKZLMZVDDFJKZOKZLMZNZIZVHBAJKZOKZLMZVJEDJKZOKZLMZNZIZIZABNZPZBCNZPZIZACNZPZIZVHWJQKZRHZPZIZIZDENZPZEFNZPZIZDFNZPZIZVJWMQKZRHZPZIZIZVGVAYDVMVGYDWAVMYDWIWAYDWQWIYDWQWQYDXKWQXKYCSXKWRWQWRXJSUPWQTUAUAWQWQUBYDWQUCUDUEWIWPSUAWAWHSUAVMVTSUAVGVLSUAVAVFSUA $.
$}
