$( tests/stdlib/polynomials/a-polynomial-real-at-a-real, elaborated from tests/stdlib/polynomials.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.polynomials.a-polynomial-real-at-a-real $p |- ( ( ( A : CC --> CC /\ A e. ( Poly ` ZZ ) ) /\ B e. RR ) -> ( A ` B ) e. RR ) $=
    ( cc wf cz cply cfv wcel wa cr simpl simpr syl gplyzre ) CCADZAEFGZHZIZBJHZIZBATRQRSKOQLMRSLN $.
$}
