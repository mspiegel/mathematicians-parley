$( tests/stdlib/counting/factorial-step, elaborated from tests/stdlib/counting.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  factori1 $p |- ( A e. NN -> ( ! ` ( A + 1 ) ) = ( ( ! ` A ) x. ( A + 1 ) ) ) $=
    ( cn wcel cn0 c1 caddc co cfa cfv cmul wceq id nnnn0 syl facp1 ) ABCZADCZAEFGZHIAHIRJGKPPQPLAMNAON $.
$}
