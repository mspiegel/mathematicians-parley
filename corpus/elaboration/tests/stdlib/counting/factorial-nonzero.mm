$( tests/stdlib/counting/factorial-nonzero, elaborated from tests/stdlib/counting.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.counting.factorial-nonzero $p |- ( A e. NN0 -> -. ( ! ` A ) = 0 ) $=
    ( cn0 wcel cfa cfv cc0 wne wceq wn id facne0 syl wb df-ne a1i mpbid ) ABCZADEZFGZRFHZIZQQSQJAKLSUAMQRFNOP $.
$}
