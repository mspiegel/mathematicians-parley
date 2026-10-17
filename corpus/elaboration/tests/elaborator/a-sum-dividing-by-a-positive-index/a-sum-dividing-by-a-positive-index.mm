$( tests/elaborator/a-sum-dividing-by-a-positive-index/a-sum-dividing-by-a-positive-index, elaborated from tests/elaborator/a-sum-dividing-by-a-positive-index.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d j k m $.
  $d A j k m $.
  tests.elaborator.a-sum-dividing-by-a-positive-index.a-sum-dividing-by-a-positive-index $p |- ( ( A e. NN /\ A. k e. ( 1 ... A ) 0 <_ ( 1 / k ) ) -> sum_ k e. ( 1 ... A ) 0 <_ sum_ k e. ( 1 ... A ) ( 1 / k ) ) $=
    ( cn wcel cc0 c1 cv cdiv co cle wbr cfz wral wa vm csu cfn fzfi a1i cr 0re 1re simpr elfznn syl nnre wne nnne0 redivcld simpl wi wceq id oveq2d breq2d rspcv mpd fsumle wb vj eqid cbvsumv breq1i breq2i bitri mpbid ) ACDZEFBGZHIZJKZBFALIZMZNZVKEOPZVKFOGZHIZOPZJKZVKEBPZVKVIBPZJKZVMVKEVPOVKQDVMFARSETDVMVOVKDZNZUASWCFVOFTDWCUBSWCVOCDZVOTDWCWBWDVMWBUCZVOAUDZUEZVOUFUEWCWDVOEUGWGVOUHUEUIWCVLEVPJKZWCVMVLVMWBUJVGVLUCUEWCWBVLWHUKWEVJWHBVOVKVHVOULZVIVPEJWIVHVOFHWIUMUNUOUPUEUQURVRWAUSVMVRVKEUTPZVKFUTGZHIZUTPZJKZWAVRWJVQJKWNVNWJVQJVKEEOUTEEULZVOWKULZEVAZSVBVCVQWMWJJVKVPWLOUTWPVOWKFHWPUMUNVBVDVEWNVSWMJKWAWJVSWMJVKEEUTBWOWKVHULZWQSVBVCWMVTVSJVKWLVIUTBWRWKVHFHWRUMUNVBVDVEVESVF $.
$}
