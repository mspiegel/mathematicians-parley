$( tests/stdlib/divisibility/mod-real, elaborated from tests/stdlib/divisibility.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.divisibility.mod-real $p |- ( ( ( A e. RR /\ B e. RR ) /\ 0 < B ) -> ( A mod B ) e. RR ) $=
    ( cr wcel wa cc0 clt wbr w3a cmo co simpl id syl simpr 3jca gmodcl ) ACDZBCDZEZFBGHZEZRSUAIABJKCDUBRSUAUBTRTUALZTRRRSLRMNNUBTSUCRSONTUAOPABQN $.
$}
