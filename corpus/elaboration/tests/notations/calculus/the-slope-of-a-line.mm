$( tests/notations/calculus/the-slope-of-a-line, elaborated from tests/notations/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d j k x $.
  $d A j k x $.
  tests.notations.calculus.the-slope-of-a-line $p |- ( ( A : ( 0 [,] 1 ) --> RR /\ A. x e. ( 0 [,] 1 ) ( A ` x ) = ( 2 x. x ) ) -> A. x e. ( 0 (,) 1 ) ( ( RR _D A ) ` x ) = 2 ) $=
    ( cc0 c1 cicc co cr wf cv cfv c2 cmul wceq wral wa vk cdv cioo wcel wss 0re a1i 1re jca iccssre syl ioossicc crn ctg iooretop 2re simpl id simpr wb vj fveq2d oveq2d eqeq12d cbvralvw bitri mpbid gdvlinv eqeq1d ) CDEFZGBHZAIZBJZKVGLFZMZAVENZOZPIZGBQFZJZKMZPCDRFZNZVGVNJZKMZAVQNZVLPVEVQBKVLCGSZDGSZOVEGTVLWBWCWBVLUAUBWCVLUCUBUDCDUEUFVQVETVLCDUGUBVQRUHUIJSVLCDUJUBKGSVLUKUBVLVFVFVFVKULVFUMUFVLVKVMBJZKVMLFZMZPVENZVFVKUNVKWGUOVLVKUPIZBJZKWHLFZMZUPVENWGVJWKAUPVEVGWHMZVHWIVIWJWLVGWHBWLUMZUQWLVGWHKLWMURUSUTWKWFUPPVEWHVMMZWIWDWJWEWNWHVMBWNUMZUQWNWHVMKLWOURUSUTVAUBVBVCVRWAUOVLVRWHVNJZKMZUPVQNWAVPWQPUPVQVMWHMZVOWPKWRVMWHVNWRUMUQVDUTWQVTUPAVQWHVGMZWPVSKWSWHVGVNWSUMUQVDUTVAUBVB $.
$}
