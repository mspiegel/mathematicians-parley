$( tests/elaborator/an-exhibit-from-an-and/two-witnesses-from-an-and, elaborated from tests/elaborator/an-exhibit-from-an-and.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d x y $.
  $d A x y $.
  $d B x y $.
  $d C x y $.
  tests.elaborator.an-exhibit-from-an-and.two-witnesses-from-an-and $p |- ( ( ( A e. _V /\ B e. A ) /\ C e. ( A \ { B } ) ) -> E. x e. A E. y e. A -. x = y ) $=
    ( cvv wcel wa csn cdif cv wceq wn wrex simpl simpr syl wne eldifsn sylib wb df-ne a1i anbi2d mpbid neqcomd jca id eqeq2d notbid rspcev eqeq1d rexbidva ) CFGZDCGZHZECDIZJZGZHZUODBKZLZMZBCNZHAKZVALZMZBCNZACNUTUOVDUTUPUOUPUSOUNUOPQUTECGZDELZMZHVDUTVIVKUTVIEDLZMZHZVIUTVIEDRZHZVNUTUSVPUPUSPZECDSZTZUTVOVMVIVOVMUAZUTEDUBZUCZUDZUEZVIVMOQUTEDUTVNVMWDVIVMPQUFUGVCVKBECVAELZVBVJWEVAEDWEUHUIUJUKQUGVHVDADCVEDLZVGVCBCWFVACGZHZVFVBWHVEDVAWHWFWFWFWGOWFUHQULUJUMUKQ $.
$}
