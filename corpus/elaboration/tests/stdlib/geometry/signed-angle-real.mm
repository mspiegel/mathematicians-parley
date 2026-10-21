$( tests/stdlib/geometry/signed-angle-real, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.signed-angle-real $p |- ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ -. A = B ) /\ -. C = B ) -> ( ( A - B ) ang ( C - B ) ) <_ _pi ) $=
    ( cc wcel wa wceq wn cmin co cang cr cpi cneg clt wbr cle w3a wne simpl simpr syl neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid jca wi id 3jca gsangcl mpd simp3 ) ADEZBDEZFZCDEZFZABGZHZFZCBGZHZFZABIJZCBIJZKJZLEZMNZVLOPZVLMQPZRZVPVIABSZCBSZFZVQVIVRVSVIBAGZHZVRVIABVIVFVEVFVHTZVCVEUAUBUCVIVRWBVIVRVEWBVRVEUDVIABUEUFVIVDWAVIWAVDWAVDUDVIBAUGUFUHUIUJUHUKVIBCGZHZVSVICBVFVHUAUCVIVSWEVIVSVHWEVSVHUDVICBUEUFVIVGWDVGWDUDVICBUGUFUIUJUHUKULVIUSUTVBRVTVQUMVIUSUTVBVIVFUSWCVFVCUSVCVETZVCVAUSVAVBTZVAUSUSUSUTTUSUNUBUBUBUBVIVFUTWCVFVCUTWFVCVAUTWGUSUTUAUBUBUBVIVFVBWCVFVCVBWFVAVBUAUBUBUOABCUPUBUQVMVOVPURUB $.
$}
