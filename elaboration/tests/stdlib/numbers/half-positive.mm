$( tests/stdlib/numbers/half-positive, elaborated from tests/stdlib/numbers.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  halfposi $p |- ( ( A e. RR /\ 0 < A ) -> 0 < ( A / 2 ) ) $=
    ( cr wcel cc0 clt wbr wa c2 cdiv co simpr wb simpl id syl halfpos2 mpbid ) ABCZDAEFZGZSDAHIJZEFZRSKTRSUBLTRRRSMRNOAPOQ $.
$}
