$( tests/elaborator/reading-memberships/a-range-bound-contradicted, elaborated from tests/elaborator/reading-memberships.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.reading-memberships.a-range-bound-contradicted $p |- ( ( A e. ZZ /\ B e. ( 1 ... A ) ) -> -. A < B ) $=
    ( cz wcel c1 cfz co wa clt wbr wn cle simpl simpr syl elfzle2 cr wb id zre cn elfznn nnre ltnle syl2anc mpbid pm2.21dd ex pm2.01d ) ACDZBEAFGZDZHZABIJZUMUNUNKZUMUNHZBALJZUOUPULUQUPUMULUMUNMZUJULNZOZBEAPOUPUNUQKZUMUNNUPAQDZBQDZUNVARUPUJVBUPUMUJURUMUJUJUJULMUJSOOATOUPBUADZVCUPULVDUTBAUBOBUCOABUDUEUFUGUHUI $.
$}
