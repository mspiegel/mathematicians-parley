$( tests/elaborator/notations/a-member-of-a-nonempty-set, elaborated from tests/elaborator/notations.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A a $.
  $d B a $.
  tests.elaborator.notations.a-member-of-a-nonempty-set $p |- ( ( ( A e. _V /\ B e. NN0 ) /\ ( # ` A ) = ( B + 1 ) ) -> E. a e. A T. ) $=
    ( cvv wcel cn0 wa chash cfv c1 caddc co wceq cv wex wtru wrex cc0 clt wbr simpl id syl simpr nn0p1gt0 eqcomd breq2d mpbid jca hashgt0elex wb rextru a1i ) ADEZBFEZGZAHIZBJKLZMZGZCNZAEZCOZPCAQZUTUNRUQSTZGVCUTUNVEUTUPUNUPUSUAZUPUNUNUNUOUAUNUBUCUCUTRURSTZVEUTUOVGUTUPUOVFUNUOUDUCBUEUCUTURUQRSUTUQURUPUSUDUFUGUHUICADUJUCVCVDUKUTCAULUMUH $.
$}
