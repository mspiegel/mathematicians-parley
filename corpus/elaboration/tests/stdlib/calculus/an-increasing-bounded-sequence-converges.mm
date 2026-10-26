$( tests/stdlib/calculus/an-increasing-bounded-sequence-converges, elaborated from tests/stdlib/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d j k m n $.
  $d A j k m n $.
  $d B j k m n $.
  tests.stdlib.calculus.an-increasing-bounded-sequence-converges $p |- ( ( ( ( A : NN --> RR /\ A. m e. NN ( A ` m ) <_ ( A ` ( m + 1 ) ) ) /\ B e. RR ) /\ A. m e. NN ( A ` m ) <_ B ) -> E. k e. RR ( n e. NN |-> ( A ` n ) ) ~~> k ) $=
    ( cn cr wf cv cfv c1 caddc co cle wbr wral wa wcel simpl id syl simpr wb vj wceq fveq2d oveq1d breq12d cbvralvw bitri a1i mpbid breq1d gmonolim ) FGAHZDIZAJZUPKLMZAJZNOZDFPZQZBGRZQZUQBNOZDFPZQZCBEAVGVDUOVDVFSZVDVBUOVBVCSZVBUOUOUOVASUOTUAUAUAVGVAEIZAJZVJKLMZAJZNOZEFPZVGVDVAVHVDVBVAVIUOVAUBUAUAVAVOUCVGVAUDIZAJZVPKLMZAJZNOZUDFPVOUTVTDUDFUPVPUEZUQVQUSVSNWAUPVPAWATZUFZWAURVRAWAUPVPKLWBUGUFUHUIVTVNUDEFVPVJUEZVQVKVSVMNWDVPVJAWDTZUFZWDVRVLAWDVPVJKLWEUGUFUHUIUJUKULVGVDVCVHVBVCUBUAVGVFVKBNOZEFPZVDVFUBVFWHUCVGVFVQBNOZUDFPWHVEWIDUDFWAUQVQBNWCUMUIWIWGUDEFWDVQVKBNWFUMUIUJUKULUN $.
$}
