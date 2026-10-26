$( tests/stdlib/polynomials/an-algebraic-number-is-a-root, elaborated from tests/stdlib/polynomials.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A m $.
  tests.stdlib.polynomials.an-algebraic-number-is-a-root $p |- ( ( A e. CC /\ A e. AA ) -> E. m e. ( CC ^m CC ) ( ( m e. ( Poly ` ZZ ) /\ ( deg ` m ) e. NN ) /\ ( m ` A ) = 0 ) ) $=
    ( cc wcel caa wa simpr galgroot ) ACDZAEDZFABIJGH $.
$}
