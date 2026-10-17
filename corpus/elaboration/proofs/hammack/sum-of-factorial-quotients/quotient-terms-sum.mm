$( proofs/hammack/sum-of-factorial-quotients/quotient-terms-sum, elaborated from proofs/hammack/sum-of-factorial-quotients.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d i j k $.
  $d A i j k $.
  $d B i j k $.
  proofs.hammack.sum-of-factorial-quotients.quotient-terms-sum $p |- ( ( ( A e. NN /\ B : NN --> RR ) /\ A. k e. NN ( B ` k ) = ( k / ( ! ` ( k + 1 ) ) ) ) -> sum_ k e. ( 1 ... A ) ( B ` k ) = sum_ k e. ( 1 ... A ) ( k / ( ! ` ( k + 1 ) ) ) ) $=
    ( cn wcel cr wf wa cv cfv c1 caddc co cfa cdiv wceq wral cfz vj csu simpl simpr syl wi elfznn id fveq2d oveq1d oveq12d eqeq12d rspcv mpd sumeq2dv wb vi cbvsumv eqeq1i eqeq2i bitri a1i mpbid ) ADEZDFBGZHZCIZBJZVEVEKLMZNJZOMZPZCDQZHZKARMZSIZBJZSTZVMVNVNKLMZNJZOMZSTZPZVMVFCTZVMVICTZPZVLVMVOVSSVLVNVMEZHZVKVOVSPZWFVLVKVLWEUAVDVKUBUCWFVNDEZVKWGUDWFWEWHVLWEUBVNAUEUCVJWGCVNDVEVNPZVFVOVIVSWIVEVNBWIUFZUGWIVEVNVHVROWJWIVGVQNWIVEVNKLWJUHUGUIUJUKUCULUMWAWDUNVLWAVMUOIZBJZUOTZVMWKWKKLMZNJZOMZUOTZPZWDWAWMVTPWRVPWMVTVMVOWLSUOVNWKPZVNWKBWSUFZUGUPUQVTWQWMVMVSWPSUOWSVNWKVRWOOWTWSVQWNNWSVNWKKLWTUHUGUIUPURUSWRWBWQPWDWMWBWQVMWLVFUOCWKVEPZWKVEBXAUFZUGUPUQWQWCWBVMWPVIUOCXAWKVEWOVHOXBXAWNVGNXAWKVEKLXBUHUGUIUPURUSUSUTVA $.
$}
