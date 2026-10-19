$( tests/notations/calculus/one-is-the-least-bound-of-the-unit-interval, elaborated from tests/notations/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ tests/notations/calculus/one-bounds-the-unit-interval.mm $]
$[ tests/notations/calculus/one-is-in-the-unit-interval.mm $]

${
  $d k m s t u $.
  tests.notations.calculus.one-is-the-least-bound-of-the-unit-interval $p |- ( A. s e. ( 0 [,] 1 ) s <_ 1 /\ A. t e. RR ( A. s e. ( 0 [,] 1 ) s <_ t -> 1 <_ t ) ) $=
    ( cv c1 cle wbr cc0 cicc co wral wi cr wa wtru vu tests.notations.calculus.one-bounds-the-unit-interval a1i vm wcel simpr simpl tests.notations.calculus.one-is-in-the-unit-interval syl wceq id breq1d rspcv mpd ex ralrimiva wb vk breq2d ralbidv imbi12d cbvralvw bitri mpbid jca anbi2i mptru ) BCZDEFZBGDHIZJZVBACZEFZBVDJZDVFEFZKZALJZMZNVEVBOCZEFZBVDJZDVMEFZKZOLJZMZVLNVEVRVENBPQNVBRCZEFZBVDJZDVTEFZKZRLJZVRNWDRLNVTLSZMZWBWCWGWBMZWBWCWGWBTWHDVDSZWDWHWGWIWGWBUAWGNWINWFUAWINUBQUCUCWAWCBDVDVBDUDZVBDVTEWJUEUFUGUCUHUIUJWEVRUKNWEVBULCZEFZBVDJZDWKEFZKZULLJZVRWDWORULLVTWKUDZWBWMWCWNWQWAWLBVDWQVTWKVBEWQUEZUMUNWQVTWKDEWRUMUOUPWOVQULOLWKVMUDZWMVOWNVPWSWLVNBVDWSWKVMVBEWSUEZUMUNWSWKVMDEWTUMUOUPUQQURUSVSVLUKNVSVEWPMVLVRWPVEVQWOOULLVMWKUDZVOWMVPWNXAVNWLBVDXAVMWKVBEXAUEZUMUNXAVMWKDEXBUMUOUPUTWPVKVEWOVJULALWKVFUDZWMVHWNVIXCWLVGBVDXCWKVFVBEXCUEZUMUNXCWKVFDEXDUMUOUPUTUQQURVA $.
$}
