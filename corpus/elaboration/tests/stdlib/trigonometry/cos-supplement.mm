$( tests/stdlib/trigonometry/cos-supplement, elaborated from tests/stdlib/trigonometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.trigonometry.cos-supplement $p |- ( A e. RR -> ( cos ` ( ( ( ; ; 1 8 0 x. _pi ) / ; ; 1 8 0 ) - A ) ) = -u ( cos ` A ) ) $=
    ( cr wcel c1 c8 cdc cc0 cpi cmul co cdiv cmin ccos cfv cneg wceq id gcossupp syl ) ABCZTDEFZGFZHIJUBKJALJMNAMNOPTQARS $.
$}
