$( tests/elaborator/transitivity/an-order-and-its-converse, elaborated from tests/elaborator/transitivity.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.transitivity.an-order-and-its-converse $p |- ( ( ( ( A e. RR /\ B e. RR ) /\ A <_ B ) /\ B <_ A ) -> B = A ) $=
    ( cr wcel wa cle wbr wceq simpr simpl syl jca wb id letri3 syl2anc mpbird ) ACDZBCDZEZABFGZEZBAFGZEZBAHZUCUAEZUDUCUAUBUCIUDUBUAUBUCJZTUAIKLUDSRUEUFMUDUBSUGUBTSTUAJZRSIKKUDUBRUGUBTRUHTRRRSJRNKKKBAOPQ $.
$}
