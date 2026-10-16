$( proofs/setmm/group-inverses/group-inverse-by-left, elaborated from proofs/setmm/group-inverses.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/setmm/group-inverses/group-left-inverse.mm $]
$[ proofs/setmm/group-inverses/group-left-identity.mm $]

${
  proofs.setmm.group-inverses.group-inverse-by-left $p |- ( ( ( A e. Grp /\ B e. ( Base ` A ) ) /\ C e. ( Base ` A ) ) -> ( ( ( invg ` A ) ` B ) = C <-> ( C ( +g ` A ) B ) = ( 0g ` A ) ) ) $=
    ( cgrp wcel cbs cfv wa cminusg wceq cplusg co c0g simpl id syl simpr jca proofs.setmm.group-inverses.group-left-inverse oveq1d eqeq1d mpbid eqid grpinvcl proofs.setmm.group-inverses.group-left-identity eqcomd eqtrd w3a 3jca grpass grprinv oveq2d grprid impbida ) ADEZBAFGZEZHZCUPEZHZBAIGZGZCJZCBAKGZLZAMGZJZUTVCHZVBBVDLZVFJZVGVHURVJVHUOUQVHUTUOUTVCNZUTURUOURUSNZURUOUOUOUQNZUOOZPZPZPVHUTUQVKUTURUQVLUOUQQZPZPRABSPVHVIVEVFVHVBCBVDUTVCQTUAUBUTVGHZVBCVFVDLZCVSVBCBVBVDLZVDLZVTVSVBVEVBVDLZWBVSVBVFVBVDLZWCVSWDVBVSUOVBUPEZHWDVBJVSUOWEVSUTUOUTVGNZVPPZVSURWEVSUOUQWGVSUTUQWFVRPZRZUPAVABUPUCZVAUCZUDZPZRAVBUEPUFVSWCWDVSVEVFVBVDUTVGQTUFUGVSUOUSUQWEUHZHWCWBJVSUOWNWGVSUSUQWEVSUTUSWFURUSQZPZWHWMUIRUPVDACBVBWJVDUCZUJPUGVSVTWBVSVFWACVDVSWAVFVSURWAVFJWIUPVDAVABVFWJWQVFUCZWKUKPUFULUFUGVSUOUSHVTCJVSUOUSWGWPRUPVDACVFWJWQWRUMPUGUN $.
$}
