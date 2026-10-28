$( tests/stdlib/polynomials/a-number-not-algebraic-is-transcendental, elaborated from tests/stdlib/polynomials.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.polynomials.a-number-not-algebraic-is-transcendental $p |- ( ( A e. CC /\ -. A e. AA ) -> ( A e. CC /\ -. A e. AA ) ) $=
    ( cc wcel caa wn wa simpr wb simpl id syl gtransc mpbird ) ABCZADCZEZFZQPNPGQNQPHQNNNPINJKALKM $.
$}
