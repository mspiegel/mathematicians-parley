$( proofs/setmm/group-cancellation/left-cancellation, elaborated from proofs/setmm/group-cancellation.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/setmm/group-cancellation/the-left-inverse.mm $]
$[ proofs/setmm/group-cancellation/the-left-identity.mm $]

${
  proofs.setmm.group-cancellation.left-cancellation $p |- ( ( ( ( A e. Grp /\ B e. ( Base ` A ) ) /\ C e. ( Base ` A ) ) /\ D e. ( Base ` A ) ) -> ( ( D ( +g ` A ) B ) = ( D ( +g ` A ) C ) <-> B = C ) ) $=
    ( cgrp wcel cbs cfv wa cplusg co wceq c0g cminusg simpl id syl simpr jca proofs.setmm.group-cancellation.the-left-identity eqcomd w3a eqid grpinvcl 3jca grpass proofs.setmm.group-cancellation.the-left-inverse oveq1d eqeq1d mpbid oveq2d eqeq2d eqtrd impbida ) AEFZBAGHZFZIZCUPFZIZDUPFZIZDBAJHZKZDCVCKZLZBCLZVBVFIZBAMHZCVCKZCVHBDANHZHZVEVCKZVJVHBVIBVCKZVMVHVNBVHURVNBLVHUOUQVHVBUOVBVFOZVBUTUOUTVAOZUTURUOURUSOZURUOUOUOUQOZUOPZQZQZQZQZVHVBUQVOVBUTUQVPUTURUQVQUOUQRZQZQZQZSABTQUAVHVNVLVDVCKZLZVNVMLVHVLDVCKZBVCKZWHLZWIVHUOVLUPFZVAUQUBZIWLVHUOWNWCVHWMVAUQVHUOVAIZWMVHUOVAWCVHVBVAVOUTVARZQZSZUPAVKDUPUCZVKUCZUDZQZWQWGUESUPVCAVLDBWSVCUCZUFQVHWKVNWHVHWJVIBVCVHWOWJVILZWRADUGZQZUHUIUJVHWHVMVNVHVDVEVLVCVBVFRUKULUJUMVHVJVMVHWJCVCKZVMLZVJVMLVHUOWMVAUSUBZIXHVHUOXIWCVHWMVAUSXBWQVHVBUSVOVBUTUSVPURUSRZQZQZUESUPVCAVLDCWSXCUFQVHXGVJVMVHWJVICVCXFUHUIUJUAUMVHUOUSIVJCLVHUOUSWCXLSACTQUMVBVGIBCDVCVBVGRUKUN $.
$}
