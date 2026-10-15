$( tests/docs/syntax/triangle-by-cases, elaborated from tests/docs/syntax.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/wiedijk/triangle-inequality/abs-bounds.mm $]
$[ tests/docs/syntax/sum-nonneg-bounded.mm $]
$[ tests/docs/syntax/sum-neg-bounded.mm $]

${
  tests.docs.syntax.triangle-by-cases $p |- ( ( A e. RR /\ B e. RR ) -> ( abs ` ( A + B ) ) <_ ( ( abs ` A ) + ( abs ` B ) ) ) $=
    ( cr wcel wa cc0 caddc co cle wbr cabs cfv clt simpl id syl simpr jca tests.docs.syntax.sum-nonneg-bounded tests.docs.syntax.sum-neg-bounded wo 0re a1i readdcld lelttric mpjaodan ) ACDZBCDZEZFABGHZIJZUJKLZAKLZBKLZGHZIJZUJFMJZUIUKEZURUPURUIUKURUGUHURUIUGUIUKNZUIUGUGUGUHNZUGOZPZPURUIUHUSUGUHQZPRUIUKQRABSPUIUQEZVDUPVDUIUQVDUGUHVDUIUGUIUQNZVBPVDUIUHVEVCPRUIUQQRABTPUIFCDZUJCDZEUKUQUAUIVFVGVFUIUBUCUIABVBVCUDRFUJUEPUF $.
$}
