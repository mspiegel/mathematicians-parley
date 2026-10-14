$( tests/stdlib/sets/nonempty-member, elaborated from tests/stdlib/sets.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A a $.
  tests.stdlib.sets.nonempty-member $p |- ( ( A e. _V /\ -. A = (/) ) -> E. a e. A T. ) $=
    ( cvv wcel c0 wceq wn wa cv wex wtru wrex wne simpr neqcomd wb df-ne a1i eqcom notbid bitrd bicomd mpbid n0 sylib rextru ) ACDZAEFZGZHZBIZADZBJZKBALZUJAEMZUMUJEAFZGZUOUJAEUGUINOUJUOUQUJUOUIUQUOUIPUJAEQRUJUHUPUHUPPUJAESRTUAUBUCBAUDUEUMUNPUJBAUFRUC $.
$}
