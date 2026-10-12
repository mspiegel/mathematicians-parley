$( tests/notations/trigonometry/cosine-of-zero, elaborated from tests/notations/trigonometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.notations.trigonometry.cosine-of-zero $p |- ( cos ` 0 ) = 1 $=
    ( cc0 ccos cfv c1 wceq wtru cos0 a1i mptru ) ABCZDEZKFGHI $.
$}
