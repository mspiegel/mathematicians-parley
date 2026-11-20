$( tests/elaborator/a-cited-codomain/a-cited-codomain, elaborated from tests/elaborator/a-cited-codomain.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d k m s t x y $.
  $d A k m s t x y $.
  $d B k m s t x y $.
  $d C k m s t x y $.
  $d D k m s t x y $.
  tests.elaborator.a-cited-codomain.a-cited-codomain $p |- ( ( ( ( A e. _V /\ B e. _V ) /\ C e. _V ) /\ D : A --> { C } ) -> ( D : A -1-1-> B -> A. s e. A A. t e. A ( ( D ` s ) = ( D ` t ) -> s = t ) ) ) $=
    ( cvv wcel wa csn wf wf1 cv cfv wceq wi wral vx vy simpr wb dff13 a1i mpbid simprd vm vk id fveq2d eqeq2d imbi12d cbvralvw ralbii simpl syl eqeq1d ralbidva bitri ex ) BGHZCGHZIZDGHZIZBDJZEKZIZBCELZFMZENZAMZENZOZVIVKOZPZABQZFBQZVGVHIZRMZENZSMZENZOZVSWAOZPZSBQZRBQZVQVRBCEKZWGVRVHWHWGIZVGVHTVHWIUAVRRSBCEUBUCUDUEWGVQUAVRWGUFMZENZUGMZENZOZWJWLOZPZUGBQZUFBQZVQWGVTWMOZVSWLOZPZUGBQZRBQWRWFXBRBWEXASUGBWAWLOZWCWSWDWTXCWBWMVTXCWAWLEXCUHZUIUJXCWAWLVSXDUJUKULUMXBWQRUFBVSWJOZXAWPUGBXEWLBHZIZWSWNWTWOXGVTWKWMXGVSWJEXGXEXEXEXFUNZXEUHZUOZUIUPXGVSWJWLXJUPUKUQULURWRWKVLOZWJVKOZPZABQZUFBQVQWQXNUFBWPXMUGABWLVKOZWNXKWOXLXOWMVLWKXOWLVKEXOUHZUIUJXOWLVKWJXPUJUKULUMXNVPUFFBWJVIOZXMVOABXQVKBHZIZXKVMXLVNXSWKVJVLXSWJVIEXSXQXQXQXRUNZXQUHZUOZUIUPXSWJVIVKYBUPUKUQULURURUCUDUS $.
$}
