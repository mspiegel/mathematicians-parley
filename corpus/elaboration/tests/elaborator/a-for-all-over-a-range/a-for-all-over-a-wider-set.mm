$( tests/elaborator/a-for-all-over-a-range/a-for-all-over-a-wider-set, elaborated from tests/elaborator/a-for-all-over-a-range.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d b i j m $.
  $d A b i j m $.
  $d B b i j m $.
  tests.elaborator.a-for-all-over-a-range.a-for-all-over-a-wider-set $p |- ( ( ( A e. NN /\ B e. RR ) /\ A. i e. NN ( i / B ) e. RR ) -> sum_ j e. ( 1 ... ( A + 1 ) ) ( j / B ) = ( sum_ j e. ( 1 ... A ) ( j / B ) + ( ( A + 1 ) / B ) ) ) $=
    ( cn wcel cr wa cv cdiv co wral c1 caddc cfz vb csu wceq cuz cfv simpl id syl elnnuz sylib cc simpr wi elfznn oveq1d eleq1d rspcv mpd recn fsump1 wb vm cbvsumv eqeq1i oveq1i eqeq2i bitri a1i mpbid ) AEFZBGFZHZCIZBJKZGFZCELZHZMAMNKZOKZPIZBJKZPQZMAOKZVPPQZVMBJKZNKZRZVNDIZBJKZDQZVRWDDQZVTNKZRZVLVPVTPMAVLVEAMSTFVLVGVEVGVKUAVGVEVEVEVFUAVEUBUCUCAUDUEVLVOVNFZHZVPGFZVPUFFWJVKWKWJVLVKVLWIUAVGVKUGUCWJVOEFZVKWKUHWJWIWLVLWIUGVOVMUIUCVJWKCVOEVHVORZVIVPGWMVHVOBJWMUBUJUKULUCUMVPUNUCVOVMRZVOVMBJWNUBUJUOWBWHUPVLWBVNUQIZBJKZUQQZVRWPUQQZVTNKZRZWHWBWQWARWTVQWQWAVNVPWPPUQVOWORZVOWOBJXAUBZUJZURUSWAWSWQVSWRVTNVRVPWPPUQXCURUTVAVBWTWEWSRWHWQWEWSVNWPWDUQDWOWCRZWOWCBJXDUBZUJZURUSWSWGWEWRWFVTNVRWPWDUQDXFURUTVAVBVBVCVD $.
$}
