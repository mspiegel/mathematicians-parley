$( tests/elaborator/a-theorem-cited-at-a-raised-power/a-square-of-a-product, elaborated from tests/elaborator/a-theorem-cited-at-a-raised-power.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.a-theorem-cited-at-a-raised-power.a-square-of-a-product $p |- ( ( A e. RR /\ B e. RR ) -> ( ( A x. B ) ^ 2 ) = ( ( A ^ 2 ) x. ( B ^ 2 ) ) ) $=
    ( cr wcel wa cc c2 cn0 w3a cmul co cexp wceq simpl id syl recn simpr 2nn0 a1i 3jca mulexp ) ACDZBCDZEZAFDZBFDZGHDZIABJKGLKAGLKBGLKJKMUEUFUGUHUEUCUFUEUCUCUCUDNUCOPAQPUEUDUGUCUDRBQPUHUESTUAABGUBP $.
$}
