$( tests/stdlib/geometry/distance-of-points-by-coordinates, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.distance-of-points-by-coordinates $p |- ( ( ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. RR ) /\ D e. RR ) /\ E e. RR ) /\ F e. RR ) /\ A = ( C + ( _i x. D ) ) ) /\ B = ( E + ( _i x. F ) ) ) -> ( abs ` ( A - B ) ) = ( sqrt ` ( ( ( C - E ) ^ 2 ) + ( ( D - F ) ^ 2 ) ) ) ) $=
    ( cc wcel wa cr ci cmul co caddc wceq cmin cabs cfv c2 cexp csqrt simpl simpr syl jca wi gptdist mpd ) AGHZBGHZIZCJHZIZDJHZIZEJHZIZFJHZIZACKDLMZNMZOZIZBEKFLMZNMZOZIZVBVFIZABPMZQRZCEPMZSTMZDFPMZSTMZNMZUARZOZVGVBVFVGVCVBVCVFUBZUSVBUCUDVCVFUCUEVGULUNIZUPURIZIVHVQUFVGVSVTVGULUNVGVCULVRVCUSULUSVBUBZUSUQULUQURUBZUQUOULUOUPUBZUOUMULUMUNUBUKULUCUDUDUDUDUDVGVCUNVRVCUSUNWAUSUQUNWBUQUOUNWCUMUNUCUDUDUDUDUEVGUPURVGVCUPVRVCUSUPWAUSUQUPWBUOUPUCUDUDUDVGVCURVRVCUSURWAUQURUCUDUDUEUEABCDEFUGUDUH $.
$}
