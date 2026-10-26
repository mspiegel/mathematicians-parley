$( tests/stdlib/calculus/a-power-is-continuous, elaborated from tests/stdlib/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d k m y $.
  $d A k m y $.
  $d B k m y $.
  tests.stdlib.calculus.a-power-is-continuous $p |- ( ( ( A e. ~P RR /\ B : A --> RR ) /\ A. y e. A ( B ` y ) = ( y ^ 3 ) ) -> ( B |` A ) e. ( A -cn-> RR ) ) $=
    ( cr cpw wcel wf wa cv cfv c3 cexp co wceq wral vm wss simpl id syl elpwi cn0 3nn0 a1i simpr wb vk fveq2d oveq1d eqeq12d cbvralvw bitri mpbid gcncfexpres ) BDEZFZBDCGZHZAIZCJZUSKLMZNZABOZHZPBCKVDUPBDQVDURUPURVCRZURUPUPUPUQRUPSTTBDUATKUBFVDUCUDVDURUQVEUPUQUETVDVCPIZCJZVFKLMZNZPBOZURVCUEVCVJUFVDVCUGIZCJZVKKLMZNZUGBOVJVBVNAUGBUSVKNZUTVLVAVMVOUSVKCVOSZUHVOUSVKKLVPUIUJUKVNVIUGPBVKVFNZVLVGVMVHVQVKVFCVQSZUHVQVKVFKLVRUIUJUKULUDUMUN $.
$}
