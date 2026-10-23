$( tests/elaborator/a-proof-block-ending-impossible/nothing-below-one-is-two, elaborated from tests/elaborator/a-proof-block-ending-impossible.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d k m x $.
  tests.elaborator.a-proof-block-ending-impossible.nothing-below-one-is-two $p |- A. x e. RR ( ( x <_ 1 /\ x = 2 ) -> x = 5 ) $=
    ( cv c1 cle wbr c2 wceq wa c5 wi cr wral wtru vm wcel simpr simpld syl breq1d mpbid clt wn 1lt2 a1i 1re 2re ltnled pm2.21dd ex ralrimiva wb vk id eqeq1d anbi12d imbi12d cbvralvw bitri mptru ) ABZCDEZUTFGZHZUTIGZJZAKLZMNBZCDEZVGFGZHZVGIGZJZNKLZVFMVLNKMVGKOZHZVJVKVOVJHZFCDEZVKVPVHVQVPVHVIVOVJPZQVPVGFCDVPVJVIVRVHVIPRSTVPCFUAEZVQUBVSVPUCUDVPCFCKOVPUEUDFKOVPUFUDUGTUHUIUJVMVFUKMVMULBZCDEZVTFGZHZVTIGZJZULKLVFVLWENULKVGVTGZVJWCVKWDWFVHWAVIWBWFVGVTCDWFUMZSWFVGVTFWGUNUOWFVGVTIWGUNUPUQWEVEULAKVTUTGZWCVCWDVDWHWAVAWBVBWHVTUTCDWHUMZSWHVTUTFWIUNUOWHVTUTIWIUNUPUQURUDTUS $.
$}
