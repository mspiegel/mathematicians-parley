$( proofs/setmm/remainder-real/remainder-is-real, elaborated from proofs/setmm/remainder-real.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A m $.
  $d B m $.
  proofs.setmm.remainder-real.remainder-is-real $p |- ( ( ( A e. RR /\ B e. RR ) /\ 0 < B ) -> ( A mod B ) e. RR ) $=
    ( cr wcel wa cc0 clt wbr vm cv cdiv co cfl cfv wceq wex cmo cvv fvex a1i elisset syl cmul cmin simpl id simpr cz wn wne 0re ltne syl2anc neneqd neqcomd wb df-ne eqcom bicomd notbid bitrd mpbid redivcld flcl eqeltrd zre remulcld resubcld w3a 3jca gmodval jca eqcomd oveq2d eqeq2d eleq1d ex exlimdv mpd ) ACDZBCDZEZFBGHZEZIJZABKLZMNZOZIPZABQLZCDZWDWGRDZWIWLWDWFMSTIWGRUAUBWDWHWKIWDWHWKWDWHEZABWEUCLZUDLZCDWKWMAWNWMWDVTWDWHUEZWDWBVTWBWCUEZWBVTVTVTWAUEZVTUFZUBZUBZUBZWMBWEWMWDWAWPWDWBWAWQVTWAUGZUBZUBZWMWEUHDZWECDWMWEWGUHWDWHUGZWMWFCDZWGUHDZWMABXBXEWMFBOZUIZBFUJZWMBFWMWDBFOZUIZWPWDBFWDFCDZWCXLXOWDUKTZWBWCUGZFBULZUMZUNZUBZUOZWMXLXKWMXLXNXKXLXNUPZWMBFUQZTZWMXMXJWMXJXMXJXMUPZWMFBURZTZUSZUTZVAZUSZVBZVCZWFVDZUBZVEZWEVFUBVGVHWMWOWJCWMWJWOWMWJABWGUCLZUDLZOZWJWOOWMVTWAWCVIYTWMVTWAWCXBXEWMWDWCWPXQUBVJABVKUBWMYSWOWJWMYRWNAUDWMWGWEBUCWMWEWGWMWHXFEWHWMWHXFXGYQVLWHXFUEUBVMVNVNVOVBVMVPVBVQVRVS $.
$}
