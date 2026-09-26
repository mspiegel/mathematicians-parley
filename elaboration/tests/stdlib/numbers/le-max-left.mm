$( tests/stdlib/numbers/le-max-left, elaborated from tests/stdlib/numbers.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  lemaxlef $p |- ( ( A e. RR /\ B e. RR ) -> A <_ if ( A <_ B , B , A ) ) $=
    ( max1 ) ABC $.
$}
