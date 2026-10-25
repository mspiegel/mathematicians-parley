$( tests/elaborator/reading-sentences/an-and-part-in-a-transitivity, elaborated from tests/elaborator/reading-sentences.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.reading-sentences.an-and-part-in-a-transitivity $p |- ( ( ( ( ( A e. RR /\ B e. RR ) /\ C e. RR ) /\ ( A = 1 /\ B <_ C ) ) /\ C < 0 ) -> B < 0 ) $=
    ( cr wcel wa c1 wceq cle wbr cc0 clt simpl simpr syl 0re a1i lelttrd ) ADEZBDEZFZCDEZFZAGHZBCIJZFZFZCKLJZFZBCKUIUGTUGUHMZUGUCTUCUFMZUCUATUAUBMSTNOOOUIUGUBUJUGUCUBUKUAUBNOOKDEUIPQUIUFUEUIUGUFUJUCUFNOUDUENOUGUHNR $.
$}
