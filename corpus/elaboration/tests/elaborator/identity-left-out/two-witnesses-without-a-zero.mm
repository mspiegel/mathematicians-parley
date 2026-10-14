$( tests/elaborator/identity-left-out/two-witnesses-without-a-zero, elaborated from tests/elaborator/identity-left-out.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d p q $.
  $d A p q $.
  $d B p q $.
  $d C p q $.
  $d D p q $.
  tests.elaborator.identity-left-out.two-witnesses-without-a-zero $p |- ( ( ( ( ( A e. ZZ /\ B e. ZZ ) /\ C e. ZZ ) /\ D e. ZZ ) /\ ( C x. B ) = ( A + D ) ) -> E. p e. ZZ E. q e. ZZ ( ( p x. B ) + 0 ) = ( A + q ) ) $=
    ( cz wcel wa cmul co caddc wceq cc0 cv wrex simpl simpr syl eqcomd cc zcn mulcld addrid eqeq2d mpbid jca id oveq2d rspcev oveq1d eqeq1d rexbidva ) AGHZBGHZIZCGHZIZDGHZIZCBJKZADLKZMZIZUQVANLKZAEOZLKZMZEGPZIFOZBJKZNLKZVGMZEGPZFGPVDUQVIVDUTUQUTVCQZUTURUQURUSQZUPUQRZSZSZVDUSVEVBMZIVIVDUSVTVDUTUSVOURUSRSVDVBVEVDVBVAMVBVEMVDVAVBUTVCRTVDVAVEVBVDVEVAVDVAUAHVEVAMVDCBVDUQCUAHVSCUBSVDUOBUAHVDUTUOVOUTURUOVPURUPUOUPUQQUNUORSSSBUBSUCVAUDSTUEUFTUGVHVTEDGVFDMZVGVBVEWAVFDALWAUHUIUEUJSUGVNVIFCGVJCMZVMVHEGWBVFGHZIZVLVEVGWDVKVANLWDVJCBJWDWBWBWBWCQWBUHSUKUKULUMUJS $.
$}
