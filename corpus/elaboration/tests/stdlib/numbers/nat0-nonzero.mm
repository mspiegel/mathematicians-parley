$( tests/stdlib/numbers/nat0-nonzero, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.nat0-nonzero $p |- ( ( A e. NN0 /\ -. A = 0 ) -> A e. NN ) $=
    ( cn0 wcel cc0 wceq wn wa wne cn simpl id syl simpr wb df-ne a1i bicomd mpbid jca elnnne0 sylibr ) ABCZADEZFZGZUBADHZGAICUEUBUFUEUBUBUBUDJUBKLUEUDUFUBUDMUEUFUDUFUDNUEADOPQRSATUA $.
$}
