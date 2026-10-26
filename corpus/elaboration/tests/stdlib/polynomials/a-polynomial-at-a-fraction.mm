$( tests/stdlib/polynomials/a-polynomial-at-a-fraction, elaborated from tests/stdlib/polynomials.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.polynomials.a-polynomial-at-a-fraction $p |- ( ( ( ( A : CC --> CC /\ A e. ( Poly ` ZZ ) ) /\ B e. ZZ ) /\ C e. NN ) -> ( ( C ^ ( deg ` A ) ) x. ( A ` ( B / C ) ) ) e. ZZ ) $=
    ( cc wf cz cply cfv wcel wa cn simpl simpr syl gaalioulem1 ) DDAEZAFGHZIZJZBFIZJZCKIZJZABCUCUARUAUBLZUASRSTLPRMNNUCUATUDSTMNUAUBMO $.
$}
