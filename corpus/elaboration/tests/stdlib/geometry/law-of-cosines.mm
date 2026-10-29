$( tests/stdlib/geometry/law-of-cosines, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.law-of-cosines $p |- ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ -. A = B ) /\ -. C = B ) /\ -. A = C ) -> ( ( abs ` ( C - A ) ) ^ 2 ) = ( ( ( ( abs ` ( A - B ) ) ^ 2 ) + ( ( abs ` ( B - C ) ) ^ 2 ) ) - ( 2 x. ( ( ( abs ` ( A - B ) ) x. ( abs ` ( B - C ) ) ) x. ( cos ` ( abs ` ( ( A - B ) ang ( C - B ) ) ) ) ) ) ) ) $=
    ( cc wcel wa wceq wn w3a cmin co cabs cfv c2 cexp caddc cmul cang ccos simpl id syl simpr 3jca jca glawcos ) ADEZBDEZFZCDEZFZABGZHZFZCBGZHZFZACGZHZFZUGUHUJIZUMUPFZFCAJKLMNOKABJKZLMZNOKBCJKZLMZNOKPKNVDVFQKVCCBJKRKLMSMQKQKJKGUTVAVBUTUGUHUJUTUQUGUQUSTZUQUNUGUNUPTZUNUKUGUKUMTZUKUIUGUIUJTZUIUGUGUGUHTUGUAUBUBUBUBUBUTUQUHVGUQUNUHVHUNUKUHVIUKUIUHVJUGUHUCUBUBUBUBUTUQUJVGUQUNUJVHUNUKUJVIUIUJUCUBUBUBUDUTUMUPUTUQUMVGUQUNUMVHUKUMUCUBUBUTUQUPVGUNUPUCUBUEUEABCUFUB $.
$}
