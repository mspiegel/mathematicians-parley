$( tests/stdlib/sums/range0-member, elaborated from tests/stdlib/sums.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  range0me $p |- ( ( A e. NN0 /\ B e. RR ) -> ( B e. ( 0 ... A ) <-> ( B e. NN0 /\ B <_ A ) ) ) $=
    ( cn0 wcel cr wa cc0 cfz co cle wbr wb simpl id syl fznn0 ) ACDZBEDZFZQBGAHIDBCDBAJKFLSQQQRMQNOBAPO $.
$}
