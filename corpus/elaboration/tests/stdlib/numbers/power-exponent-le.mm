$( tests/stdlib/numbers/power-exponent-le, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.numbers.power-exponent-le $p |- ( ( ( ( ( A e. RR /\ B e. NN0 ) /\ C e. NN0 ) /\ 1 <_ A ) /\ B <_ C ) -> ( A ^ B ) <_ ( A ^ C ) ) $=
    ( cr wcel cn0 wa c1 cle wbr simpl id syl simpr gleexp2 ) ADEZBFEZGZCFEZGZHAIJZGZBCIJZGZABCUDUBPUBUCKZUBTPTUAKZTRPRSKZRPPPQKPLMMMMUDUBQUEUBTQUFTRQUGPQNMMMUDUBSUEUBTSUFRSNMMUDUBUAUETUANMUBUCNO $.
$}
