$( tests/elaborator/a-sum-lemma-over-another-bound-letter/a-sum-termwise-over-another-letter, elaborated from tests/elaborator/a-sum-lemma-over-another-bound-letter.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d i j $.
  $d A i j $.
  tests.elaborator.a-sum-lemma-over-another-bound-letter.a-sum-termwise-over-another-letter $p |- ( A e. NN -> sum_ j e. ( 1 ... A ) ( j + j ) = sum_ j e. ( 1 ... A ) ( 2 x. j ) ) $=
    ( cn wcel c1 cfz co cv caddc c2 cmul wa vi wceq wral simpl cexp cc simpr elfznn syl nncn exp1 eqcomd cn0 1nn0 a1i expcld mullid eqtrd oveq12d eqidd ax-1cn adddir syl3anc 1p1e2 oveq1d 2cn mulridi jca mul4 eqtr4d ralrimiva wi id oveq2d eqeq12d rspcv mpd sumeq2dv ) ACDZEAFGZBHZVMIGZJVMKGZBVKVMVLDZLZMHZVRIGZJVRKGZNZMVLOZVNVONZVQVKWBVKVPPVKWAMVLVKVRVLDZLZVSJVREQGZKGZVTWEVSEWFKGZWHIGZWGWEVRWHVRWHIWEVRWFWHWEWFVRWEVRRDZWFVRNZWEVRCDZWJWEWDWLVKWDSZVRATZUAZVRUBZUAZVRUCZUAZUDZWEWHWFWEWFRDZWHWFNZWEVREWQEUEDZWEUFUGZUHZWFUIZUAZUDZUJZXIUKWEWIWIWGWEWIULWEWIEEIGZWFKGZWGWEXKWIWEERDZXLXAXKWINXLWEUMUGZXMXEEEWFUNUOUDWEXJJWFKXJJNWEUPUGUQUJUJUJWEVTJEKGZWHKGZWGWEJXNVRWHKWEXNJXNJNZWEJURUSZUGZUDXIUKWEXOXOWGWEJRDZXLLZXLXALZLXOXONWEXTYAWEXSXLXSWEURUGXMUTWEXLXAXMXEUTUTJEEWFVAUAWEXNJWHWFKXRXGUKUJUJVBVCUAVQVPWBWCVDVKVPSWAWCMVMVLVRVMNZVSVNVTVOYBVRVMVRVMIYBVEZYCUKYBVRVMJKYCVFVGVHUAVIVJ $.
$}
