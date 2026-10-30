$( tests/notations/sums/a-sum-over-a-range-written-as-a-set, elaborated from tests/notations/sums.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A k $.
  $d B k $.
  tests.notations.sums.a-sum-over-a-range-written-as-a-set $p |- ( ( A e. NN /\ B : ( 1 ... ( A + 1 ) ) --> RR ) -> sum_ k e. ( 1 ... ( A + 1 ) ) ( B ` k ) = ( sum_ k e. ( 1 ... A ) ( B ` k ) + ( B ` ( A + 1 ) ) ) ) $=
    ( cn wcel c1 caddc co cfz cr wf wa cv cfv cuz simpl id syl elnnuz sylib cc simpr ffvelcdm syl2anc recn wceq fveq2d fsump1 ) ADEZFAFGHZIHZJBKZLZCMZBNZUJBNCFAUMUIAFONEUMUIUIUIULPUIQRASTUMUNUKEZLZUOJEZUOUAEUQULUPURUQUMULUMUPPUIULUBRUMUPUBUKJUNBUCUDUOUERUNUJUFZUNUJBUSQUGUH $.
$}
