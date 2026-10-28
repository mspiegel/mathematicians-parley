$( tests/notations/calculus/one-is-the-least-bound-of-the-unit-interval, elaborated from tests/notations/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ tests/notations/calculus/one-bounds-the-unit-interval.mm $]
$[ tests/notations/calculus/one-is-in-the-unit-interval.mm $]

${
  $d k m s u $.
  tests.notations.calculus.one-is-the-least-bound-of-the-unit-interval $p |- ( A. s e. ( 0 [,] 1 ) s <_ 1 /\ A. u e. RR ( A. s e. ( 0 [,] 1 ) s <_ u -> 1 <_ u ) ) $=
    ( cv c1 cle wbr cc0 cicc co wral wi cr wa wtru tests.notations.calculus.one-bounds-the-unit-interval a1i vm wcel simpr wb biid mpbid simpl tests.notations.calculus.one-is-in-the-unit-interval syl wceq id breq1d rspcv mpd ex ralrimiva vk breq2d ralbidva imbi12d cbvralvw bitri jca mpbird mptru ) BCZDEFZBGDHIZJZVBACZEFZBVDJZDVFEFZKZALJZMZNVLVLNVEVKVENBOPNVBQCZEFZBVDJZDVMEFZKZQLJZVKNVQQLNVMLRZMZVOVPVTVOMZVOVPWAVOVOVTVOSVOVOTWAVOUAPUBWADVDRZVQWAVTWBVTVOUCVTNWBNVSUCWBNUDPUEUEVNVPBDVDVBDUFZVBDVMEWCUGUHUIUEUJUKULVRVKTNVRVBUMCZEFZBVDJZDWDEFZKZUMLJVKVQWHQUMLVMWDUFZVOWFVPWGWIVNWEBVDWIVBVDRZMZVMWDVBEWKWIWIWIWJUCWIUGZUEUNUOWIVMWDDEWLUNUPUQWHVJUMALWDVFUFZWFVHWGVIWMWEVGBVDWMWJMZWDVFVBEWNWMWMWMWJUCWMUGZUEUNUOWMWDVFDEWOUNUPUQURPUBUSVLVLTNVLUAPUTVA $.
$}
