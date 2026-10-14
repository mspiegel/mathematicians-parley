$( tests/stdlib/numbers/square-le, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.square-le $p |- ( ( ( ( A e. RR /\ B e. RR ) /\ 0 <_ A ) /\ 0 <_ B ) -> ( A <_ B <-> ( A ^ 2 ) <_ ( B ^ 2 ) ) ) $=
    ( cr wcel wa cc0 cle wbr c2 cexp co wb simpl id syl simpr jca le2sq ) ACDZBCDZEZFAGHZEZFBGHZEZSUBEZTUDEZEABGHAIJKBIJKGHLUEUFUGUESUBUEUCSUCUDMZUCUASUAUBMZUASSSTMSNOOOUEUCUBUHUAUBPOQUETUDUEUCTUHUCUATUISTPOOUCUDPQQABRO $.
$}
