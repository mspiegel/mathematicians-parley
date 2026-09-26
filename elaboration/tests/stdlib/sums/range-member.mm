$( tests/stdlib/sums/range-member, elaborated from tests/stdlib/sums.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  rangemem $p |- ( ( A e. ZZ /\ B e. RR ) -> ( B e. ( 1 ... A ) <-> ( B e. NN /\ B <_ A ) ) ) $=
    ( cz wcel cr wa c1 cfz co cn cle wbr wb simpl id syl fznn ) ACDZBEDZFZRBGAHIDBJDBAKLFMTRRRSNROPBAQP $.
$}
