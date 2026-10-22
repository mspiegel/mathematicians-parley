$( tests/elaborator/collinear-in-any-order/a-denial-first, elaborated from tests/elaborator/collinear-in-any-order.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.elaborator.collinear-in-any-order.a-denial-first $p |- ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. CC ) /\ ( ( ( -. A = B /\ -. B = C ) /\ -. A = C ) /\ -. ( ( C - A ) / ( B - A ) ) e. RR ) ) /\ ( C = D \/ ( ( B - C ) / ( D - C ) ) e. RR ) ) -> -. A = D ) $=
    ( cc wcel wa wceq wn cmin co cdiv cr wo simpl simpr syl eqcomd eqeq2d oveq1d oveq2d eleq1d orbi12d mpbid w3a wi id 3jca gcolrotate mpd wb gtridef a1i pm2.21dd ex pm2.01d ) AEFZBEFZGZCEFZGZDEFZGZABHZIZBCHZIZGZACHZIZGZCAJKZBAJKZLKZMFZIZGZGZCDHZBCJKZDCJKZLKZMFZNZGZADHZWEWFWFIZWEWFGZVDVONZWGWHCAHZVTACJKZLKZMFZNZWIWHWDWNWHWEWDWEWFOZVRWDPQWHVSWJWCWMWHDACWHADWEWFPZRZSWHWBWLMWHWAWKVTLWHDACJWQTUAUBUCUDWHUTUQURUEWNWIUFWHUTUQURWHWEUTWOWEVRUTVRWDOZVRVCUTVCVQOZVCVAUTVAVBOZUSUTPQQQQWHWEUQWOWEVRUQWRVRVCUQWSVCVAUQWTVAUSUQUSUTOZUSUQUQUQUROUQUGQQQQQQWHWEURWOWEVRURWRVRVCURWSVCVAURWTVAUSURXAUQURPQQQQQUHCABUIQUJWHVKWIIZGZXBWHVQXCWHWEVQWOWEVRVQWRVCVQPQQVQXCUKWHABCULUMUDVKXBPQUNUOUP $.
$}
