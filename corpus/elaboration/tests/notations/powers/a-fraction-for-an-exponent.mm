$( tests/notations/powers/a-fraction-for-an-exponent, elaborated from tests/notations/powers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.notations.powers.a-fraction-for-an-exponent $p |- ( ( A e. RR /\ 0 <_ A ) -> ( A ^c ( 1 / 3 ) ) e. RR ) $=
    ( cr wcel cc0 cle wbr wa c1 c3 cdiv co w3a ccxp simpl id syl simpr 1re a1i 3re cn wne 3nn nnne0 redivcld 3jca recxpcl ) ABCZDAEFZGZUHUIHIJKZBCZLAUKMKBCUJUHUIULUJUHUHUHUINUHOPUHUIQUJHIHBCUJRSIBCUJTSUJIUACZIDUBUMUJUCSIUDPUEUFAUKUGP $.
$}
