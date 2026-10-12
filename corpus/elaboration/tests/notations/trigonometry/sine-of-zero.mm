$( tests/notations/trigonometry/sine-of-zero, elaborated from tests/notations/trigonometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.notations.trigonometry.sine-of-zero $p |- ( sin ` 0 ) = 0 $=
    ( cc0 csin cfv wceq wtru sin0 a1i mptru ) ABCZADZJEFGH $.
$}
