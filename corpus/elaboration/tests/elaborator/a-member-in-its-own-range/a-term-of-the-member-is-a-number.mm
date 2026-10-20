$( tests/elaborator/a-member-in-its-own-range/a-term-of-the-member-is-a-number, elaborated from tests/elaborator/a-member-in-its-own-range.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A k $.
  tests.elaborator.a-member-in-its-own-range.a-term-of-the-member-is-a-number $p |- ( A e. NN -> A. k e. ( 1 ... A ) ( ( k x. 2 ) + A ) e. RR ) $=
    ( cn wcel cv c2 cmul co caddc cr c1 cfz wa simpr elfznn syl nnre 2re a1i remulcld simpl id readdcld ralrimiva ) ACDZBEZFGHZAIHJDBKALHZUEUFUHDZMZUGAUJUFFUJUFCDZUFJDUJUIUKUEUINUFAOPUFQPFJDUJRSTUJUEAJDUJUEUEUEUIUAUEUBPAQPUCUD $.
$}
