$( tests/stdlib/calculus/an-integral-of-a-difference, elaborated from tests/stdlib/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d j m s y $.
  $d A j m s y $.
  $d B j m s y $.
  $d C j m s y $.
  $d D j m s y $.
  $d E j m s y $.
  tests.stdlib.calculus.an-integral-of-a-difference $p |- ( ( ( ( ( ( ( ( ( A e. RR /\ B e. RR ) /\ A < B ) /\ C : ( A [,] B ) --> RR ) /\ D : ( A [,] B ) --> RR ) /\ E : ( A [,] B ) --> RR ) /\ A. y e. ( A [,] B ) ( E ` y ) = ( ( C ` y ) - ( D ` y ) ) ) /\ ( C |` ( A [,] B ) ) e. ( ( A [,] B ) -cn-> RR ) ) /\ ( D |` ( A [,] B ) ) e. ( ( A [,] B ) -cn-> RR ) ) -> S_ [ A -> B ] ( E ` s ) _d s = ( S_ [ A -> B ] ( C ` s ) _d s - S_ [ A -> B ] ( D ` s ) _d s ) ) $=
    ( cr wcel wa clt wbr cicc co wf cv cfv cmin wceq wral cres ccncf vm simpl id syl simpr wb vj fveq2d oveq12d eqeq12d cbvralvw bitri a1i mpbid gditgsubres ) BHIZCHIZJZBCKLZJZBCMNZHDOZJZVCHEOZJZVCHFOZJZAPZFQZVJDQZVJEQZRNZSZAVCTZJZDVCUAZVCHUBNZIZJZEVCUAZVSIZJZUCGBCDEFWDWAURWAWCUDZWAVQURVQVTUDZVQVIURVIVPUDZVIVGURVGVHUDZVGVEURVEVFUDZVEVBURVBVDUDZVBUTURUTVAUDZUTURURURUSUDURUEUFUFUFUFUFUFUFUFWDWAUSWEWAVQUSWFVQVIUSWGVIVGUSWHVGVEUSWIVEVBUSWJVBUTUSWKURUSUGUFUFUFUFUFUFUFWDWAVAWEWAVQVAWFVQVIVAWGVIVGVAWHVGVEVAWIVEVBVAWJUTVAUGUFUFUFUFUFUFWDWAVDWEWAVQVDWFVQVIVDWGVIVGVDWHVGVEVDWIVBVDUGUFUFUFUFUFWDWAVFWEWAVQVFWFVQVIVFWGVIVGVFWHVEVFUGUFUFUFUFWDWAVHWEWAVQVHWFVQVIVHWGVGVHUGUFUFUFWDVPUCPZFQZWLDQZWLEQZRNZSZUCVCTZWDWAVPWEWAVQVPWFVIVPUGUFUFVPWRUHWDVPUIPZFQZWSDQZWSEQZRNZSZUIVCTWRVOXDAUIVCVJWSSZVKWTVNXCXEVJWSFXEUEZUJXEVLXAVMXBRXEVJWSDXFUJXEVJWSEXFUJUKULUMXDWQUIUCVCWSWLSZWTWMXCWPXGWSWLFXGUEZUJXGXAWNXBWORXGWSWLDXHUJXGWSWLEXHUJUKULUMUNUOUPWDWAVTWEVQVTUGUFWAWCUGUQ $.
$}
