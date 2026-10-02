$( tests/stdlib/sums/range0, elaborated from tests/stdlib/sums.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.sums.range0 $p |- ( ( ( A e. NN0 /\ B e. RR ) /\ B e. ( 0 ... A ) ) -> ( B e. NN0 /\ B <_ A ) ) $=
    ( cn0 wcel cr wa cc0 cfz co cle wbr simpr wb simpl id syl fznn0 mpbid ) ACDZBEDZFZBGAHIZDZFZUCBCDZBAJKZFZUAUCLUDSUCUGMUDUASUAUCNUASSSTNSOPPBAQPR $.
$}
