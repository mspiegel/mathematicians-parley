$( tests/elaborator/polynomials-with-integer-coefficients/a-polynomial-of-degree-three, elaborated from tests/elaborator/polynomials-with-integer-coefficients.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.polynomials-with-integer-coefficients.a-polynomial-of-degree-three $p |- ( ( ( A : CC --> CC /\ A e. ( Poly ` ZZ ) ) /\ ( deg ` A ) = 3 ) -> ( deg ` A ) = 3 ) $=
    ( cc wf cz cply cfv wcel wa cdgr c3 wceq simpr ) BBACADEFGHAIFJKL $.
$}
