$( tests/stdlib/counting/binomial-coefficient, elaborated from tests/stdlib/counting.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  binomia2 $p |- ( ( ( A e. NN0 /\ B e. ZZ ) /\ B e. ( 0 ... A ) ) -> ( A _C B ) = ( ( ! ` A ) / ( ( ! ` ( A - B ) ) x. ( ! ` B ) ) ) ) $=
    ( cn0 wcel cz wa cc0 cfz co cbc cfa cfv cmin cmul cdiv wceq simpr bcval2 syl ) ACDZBEDZFZBGAHIZDZFUDABJIAKLABMIKLBKLNIOIPUBUDQBARS $.
$}
