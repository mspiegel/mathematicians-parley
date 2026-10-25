$( tests/elaborator/reading-block-letters/a-for-all-line-in-a-transitivity, elaborated from tests/elaborator/reading-block-letters.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d k m x y $.
  $d A k m x y $.
  tests.elaborator.reading-block-letters.a-for-all-line-in-a-transitivity $p |- ( ( A e. RR /\ A. x e. RR x < ( x + 1 ) ) -> A. y e. RR ( ( y + 1 ) < A -> y < A ) ) $=
    ( cr wcel cv c1 caddc co clt wbr wral wa vm wi simpl simpr syl 1re a1i readdcld id wceq oveq1d breq12d rspcv mpd jca lttrd ex ralrimiva wb vk breq1d imbi12d cbvralvw bitri mpbid ) CDEZAFZUTGHIZJKZADLZMZNFZGHIZCJKZVECJKZOZNDLZBFZGHIZCJKZVKCJKZOZBDLZVDVINDVDVEDEZMZVGVHVRVGMZVEVFCVSVRVQVRVGPZVDVQQZRZVSVEGWBGDEVSSTUAVSVRUSVTVRVDUSVDVQPZVDUSUSUSVCPUSUBRRRVSVCVEVFJKZMZWDVSVRWEVTVRVCWDVRVDVCWCUSVCQZRZVRVCWDWGVRVQVCWDOWAVBWDAVEDUTVEUCZUTVEVAVFJWHUBZWHUTVEGHWIUDUEUFRUGUHRVCWDQRVRVGQUIUJUKVJVPULVDVJUMFZGHIZCJKZWJCJKZOZUMDLVPVIWNNUMDVEWJUCZVGWLVHWMWOVFWKCJWOVEWJGHWOUBZUDUNWOVEWJCJWPUNUOUPWNVOUMBDWJVKUCZWLVMWMVNWQWKVLCJWQWJVKGHWQUBZUDUNWQWJVKCJWRUNUOUPUQTUR $.
$}
