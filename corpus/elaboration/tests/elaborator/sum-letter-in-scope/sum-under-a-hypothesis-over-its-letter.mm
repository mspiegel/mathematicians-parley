$( tests/elaborator/sum-letter-in-scope/sum-under-a-hypothesis-over-its-letter, elaborated from tests/elaborator/sum-letter-in-scope.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d i j k m $.
  $d A i j k m $.
  tests.elaborator.sum-letter-in-scope.sum-under-a-hypothesis-over-its-letter $p |- ( ( A e. NN /\ 0 <_ sum_ k e. ( 1 ... A ) ( 1 / k ) ) -> sum_ k e. ( 1 ... ( A + 1 ) ) ( 1 / k ) e. RR ) $=
    ( cn wcel cc0 c1 cfz co cv cdiv csu cle wbr wa caddc vj cr fzfid vm wral simpl 1re a1i simpr nnre syl wceq wn wne nnne0 neneqd wb df-ne bicomd mpbid redivcld ralrimiva wi elfznn id oveq2d eleq1d rspcv mpd fsumrecl vi cbvsumv eleq1i bitri ) ACDZEFAGHZFBIZJHZBKZLMZNZFAFOHZGHZFPIZJHZPKZQDZVRVMBKZQDZVPVRVTPVPFVQRVPVSVRDZNZFSIZJHZQDZSCTZVTQDZWFVPWJVPWEUAVPWISCVPWGCDZNZFWGFQDWMUBUCWMWLWGQDVPWLUDZWGUEUFWMWGEUGZUHZWGEUIZWMWGEWMWLWQWNWGUJUFUKWMWQWPWQWPULWMWGEUMUCUNUOUPUQUFWFVSCDZWJWKURWFWEWRVPWEUDVSVQUSUFWIWKSVSCWGVSUGZWHVTQWSWGVSFJWSUTVAVBVCUFVDVEWBWDULVPWBVRFVFIZJHZVFKZQDWDWAXBQVRVTXAPVFVSWTUGZVSWTFJXCUTVAVGVHXBWCQVRXAVMVFBWTVLUGZWTVLFJXDUTVAVGVHVIUCUO $.
$}
