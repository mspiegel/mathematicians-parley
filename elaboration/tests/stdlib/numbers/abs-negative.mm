$( tests/stdlib/numbers/abs-negative, elaborated from tests/stdlib/numbers.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  absnegat $p |- ( A e. RR -> ( abs ` -u A ) = ( abs ` A ) ) $=
    ( cr wcel cc cneg cabs cfv wceq id recn syl absneg ) ABCZADCZAEFGAFGHMMNMIAJKALK $.
$}
