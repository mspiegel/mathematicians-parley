$( proofs/euclid/triangle-equality-case/triangle-equality-case, elaborated from proofs/euclid/triangle-equality-case.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/geometry/triangle-equality-between.mm $]

${
  proofs.euclid.triangle-equality-case.triangle-equality-case $p |- ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ ( ( abs ` ( A - C ) ) + ( abs ` ( C - B ) ) ) = ( abs ` ( A - B ) ) ) /\ -. C = A ) /\ -. C = B ) -> ( A =/= C /\ ( ( B - C ) / ( A - C ) ) e. RR /\ ( ( B - C ) / ( A - C ) ) < 0 ) ) $=
    ( cc wcel wa cmin co cabs cfv caddc wceq wn wne cdiv cr cc0 clt wbr w3a simpl id syl simpr jca neqcomd stdlib.geometry.triangle-equality-between ) ADEZBDEZFZCDEZFZACGHZIJZCBGHZIJZKHZABGHZIJZLZFZCALZMZFZCBLZMZFZUHUKFZUIFZACLZMZFZVFFZUTFACNBCGHZUMOHZPEVOQRSTVGVMUTVGVLVFVGVIVKVGVHUIVGUHUKVGVDUHVDVFUAZVDVAUHVAVCUAZVAULUHULUTUAZULUJUHUJUKUAZUJUHUHUHUIUAUHUBUCUCUCUCUCVGVDUKVPVDVAUKVQVAULUKVRUJUKUDUCUCUCUEVGVDUIVPVDVAUIVQVAULUIVRULUJUIVSUHUIUDUCUCUCUCUEVGCAVGVDVCVPVAVCUDUCUFUEVDVFUDUEVGVDUTVPVDVAUTVQULUTUDUCUCUEACBUGUC $.
$}
