$( tests/notations/families/a-sum-over-subsets, elaborated from tests/notations/families.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A s $.
  $d B s $.
  tests.notations.families.a-sum-over-subsets $p |- ( ( ( A e. _V /\ B e. ~P ~P A ) /\ B e. Fin ) -> sum_ s e. B 1 = ( ( # ` B ) x. 1 ) ) $=
    ( cvv wcel cpw wa cfn c1 cc csu chash cfv cmul co wceq simpr ax-1cn a1i jca fsumconst syl ) ADEZBAFZFZEZGZBHEZGZUHIJEZGBICKBLMINOPUIUHUJUGUHQUJUIRSTBICUAUB $.
$}
