$( proofs/setmm/set-order-laws/union-keeps-order, elaborated from proofs/setmm/set-order-laws.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/setmm/subset-of-union/subset-of-union.mm $]
$[ proofs/setmm/subset-of-union-right/subset-of-union-right.mm $]

${
  proofs.setmm.set-order-laws.union-keeps-order $p |- ( ( ( ( A e. _V /\ B e. _V ) /\ C e. _V ) /\ A C_ B ) -> ( A u. C ) C_ ( B u. C ) ) $=
    ( cvv wcel wa wss cun simpr simpl syl jca proofs.setmm.subset-of-union.subset-of-union sstr proofs.setmm.subset-of-union-right.subset-of-union-right unss sylib ) ADEZBDEZFZCDEZFZABGZFZABCHZGZCUEGZFACHUEGUDUFUGUDUCBUEGZFUFUDUCUHUBUCIUDSUAFUHUDSUAUDUBSUBUCJZUBTSTUAJZRSIZKZKZUDUBUAUITUAIZKZLBCMKLABUENKUDUASFUGUDUASUOUMLCBOKLACUEPQ $.
$}
