$( tests/elaborator/sum-letter-in-scope/sum-under-a-hypothesis-over-its-letter, elaborated from tests/elaborator/sum-letter-in-scope.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d j k m $.
  $d A j k m $.
  tests.elaborator.sum-letter-in-scope.sum-under-a-hypothesis-over-its-letter $p |- ( ( A e. NN /\ 0 <_ sum_ k e. ( 1 ... A ) ( 1 / k ) ) -> sum_ k e. ( 1 ... ( A + 1 ) ) ( 1 / k ) e. RR ) $=
    ( cn wcel cc0 c1 cfz co cv cdiv csu cle wbr wa caddc vm cr fzfid 1re a1i simpr elfznn syl nnre wceq wn wne nnne0 neneqd wb df-ne bicomd mpbid redivcld fsumrecl vj id oveq2d cbvsumv eleq1i bitri ) ACDZEFAGHZFBIZJHZBKZLMZNZFAFOHZGHZFPIZJHZPKZQDZVJVEBKZQDZVHVJVLPVHFVIRVHVKVJDZNZFVKFQDVRSTVRVKCDZVKQDVRVQVSVHVQUAZVKVIUBZUCZVKUDUCVRVKEUEZUFZVKEUGZVRVKEVRVSWEWBVKUHUCUIVRWEWDWEWDUJVRVKEUKTULUMUNUOVNVPUJVHVNVJFUPIZJHZUPKZQDVPVMWHQVJVLWGPUPVKWFUEZVKWFFJWIUQURUSUTWHVOQVJWGVEUPBWFVDUEZWFVDFJWJUQURUSUTVATUM $.
$}
