$( tests/stdlib/numbers/abs-zero, elaborated from tests/stdlib/numbers.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  abszero $p |- ( abs ` 0 ) = 0 $=
    ( cc0 cabs cfv wceq wtru abs0 a1i mptru ) ABCZADZJEFGH $.
$}
