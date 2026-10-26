$( tests/stdlib/numbers/abs-difference-le, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.abs-difference-le $p |- ( ( ( A e. RR /\ B e. RR ) /\ C e. RR ) -> ( ( abs ` ( A - B ) ) <_ C <-> ( ( B - C ) <_ A /\ A <_ ( B + C ) ) ) ) $=
    ( cr wcel wa w3a cmin co cabs cfv cle wbr caddc wb simpl id syl simpr 3jca absdifle ) ADEZBDEZFZCDEZFZUBUCUEGABHIJKCLMBCHIALMABCNILMFOUFUBUCUEUFUDUBUDUEPZUDUBUBUBUCPUBQRRUFUDUCUGUBUCSRUDUESTABCUAR $.
$}
