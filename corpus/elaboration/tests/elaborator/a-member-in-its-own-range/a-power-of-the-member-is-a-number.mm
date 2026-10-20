$( tests/elaborator/a-member-in-its-own-range/a-power-of-the-member-is-a-number, elaborated from tests/elaborator/a-member-in-its-own-range.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A k $.
  tests.elaborator.a-member-in-its-own-range.a-power-of-the-member-is-a-number $p |- ( A e. NN0 -> A. k e. ( 0 ... A ) ( ( 2 ^ k ) x. k ) e. RR ) $=
    ( cn0 wcel c2 cv cexp co cmul cr cc0 cfz wa 2re a1i simpr elfznn0 syl reexpcld nn0re remulcld ralrimiva ) ACDZEBFZGHZUDIHJDBKALHZUCUDUFDZMZUEUDUHEUDEJDUHNOUHUGUDCDZUCUGPZUDAQZRZSUHUIUDJDULUDTRUAUB $.
$}
