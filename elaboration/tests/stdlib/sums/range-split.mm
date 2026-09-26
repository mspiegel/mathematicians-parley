$( tests/stdlib/sums/range-split, elaborated from tests/stdlib/sums.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  rangespl $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ C e. ( A ... B ) ) -> ( A ... B ) = ( ( A ... C ) u. ( ( C + 1 ) ... B ) ) ) $=
    ( cz wcel wa cfz co c1 caddc cun wceq simpr fzsplit syl ) ADEZBDEZFZCABGHZEZFTSACGHCIJHBGHKLRTMCABNO $.
$}
