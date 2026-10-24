$( tests/notations/powers/the-cube-root-of-a-cube, elaborated from tests/notations/powers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.notations.powers.the-cube-root-of-a-cube $p |- ( A e. RR -> if ( 0 <_ ( A ^ 3 ) , ( ( A ^ 3 ) ^c ( 1 / 3 ) ) , -u ( -u ( A ^ 3 ) ^c ( 1 / 3 ) ) ) = A ) $=
    ( cr wcel cc0 c3 cexp co cle wbr c1 cdiv ccxp cneg cif wceq id gcbrtcube syl ) ABCZSDAEFGZHITJEKGZLGTMUALGMNAOSPAQR $.
$}
