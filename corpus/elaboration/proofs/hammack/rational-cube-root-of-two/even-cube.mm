$( proofs/hammack/rational-cube-root-of-two/even-cube, elaborated from proofs/hammack/rational-cube-root-of-two.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]
$[ proofs/hammack/rational-cube-root-of-two/odd-cube.mm $]

${
  proofs.hammack.rational-cube-root-of-two.even-cube $p |- ( ( A e. ZZ /\ 2 || ( A ^ 3 ) ) -> 2 || A ) $=
    ( cz wcel c2 c3 cexp co cdvds wbr wa wn wo simpl id syl gevenodd wi simpr jca proofs.hammack.rational-cube-root-of-two.odd-cube gnotboth pm2.21dd ex pm2.01d orel2 mpd ) ABCZDAEFGZHIZJZDAHIZUGUKKZJZLZUKUJUGUNUJUGUGUGUIMUGNOAPOUJUMKZUNUKQUJUMUJUMUOUJUMJZUHBCZUIKZJZUOUPUGUMJUSUPUGUMUPUMUGUJUMRZUGULMOUTSATOUPUIUSKUPUJUIUJUMMUGUIROUHUAOUBUCUDUMUKUEOUF $.
$}
