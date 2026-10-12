$( tests/notations/functions/an-inverse-value, elaborated from tests/notations/functions.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A x $.
  tests.notations.functions.an-inverse-value $p |- ( ( ( A : RR --> RR /\ A : RR -1-1-> RR ) /\ A. x e. RR ( A ` x ) = ( ( 2 x. x ) + 1 ) ) -> ( `' A ` 7 ) = 3 ) $=
    ( cr wf wf1 wa cv cfv c2 cmul co c1 caddc wceq wral c3 ccnv c7 wcel simpl id syl simpr 3re a1i jca gf1cnvfv1 wi fveq2d oveq2d oveq1d eqeq12d rspcv mpd c6 eqid oveq12i 2t3e6 eqtri 6p1e7 eqtr4i eqtrd eqeq1d mpbid ) CCBDZCCBEZFZAGZBHZIVHJKZLMKZNZACOZFZPBHZBQZHZPNZRVPHZPNVNVFPCSZFVRVNVFVTVNVGVFVNVGVGVGVMTVGUAUBVEVFUCUBVTVNUDUEZUFCCPBUGUBVNVQVSPVNVORVPVNVOIPJKZLMKZRVNVMVOWCNZVGVMUCVNVTVMWDUHWAVLWDAPCVHPNZVIVOVKWCWEVHPBWEUAZUIWEVJWBLMWEVHPIJWFUJUKULUMUBUNWCRNVNWCRRWCUOLMKRWBUOLLMWBWBUOIIPPJIUPPUPUQURUSLUPUQUTUSRUPVAUEVBUIVCVD $.
$}
