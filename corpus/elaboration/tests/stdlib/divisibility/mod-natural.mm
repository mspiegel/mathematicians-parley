$( tests/stdlib/divisibility/mod-natural, elaborated from tests/stdlib/divisibility.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.divisibility.mod-natural $p |- ( ( A e. ZZ /\ B e. NN ) -> ( A mod B ) e. NN0 ) $=
    ( cz wcel cn wa cmo co cn0 simpl id syl simpr jca zmodcl ) ACDZBEDZFZRABGHIDRPQRPPPQJPKLPQMNABOL $.
$}
