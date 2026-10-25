$( tests/elaborator/a-hypothesis-letter-from-a-triangle/a-hypothesis-letter-from-a-triangle-in-another-order, elaborated from tests/elaborator/a-hypothesis-letter-from-a-triangle.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.elaborator.a-hypothesis-letter-from-a-triangle.a-hypothesis-letter-from-a-triangle-in-another-order $p |- ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. CC ) /\ ( ( ( -. A = B /\ -. B = C ) /\ -. A = C ) /\ -. ( ( C - A ) / ( B - A ) ) e. RR ) ) /\ ( C =/= D /\ ( ( A - D ) / ( C - D ) ) e. RR /\ ( ( A - D ) / ( C - D ) ) < 0 ) ) -> ( ( ( -. B = C /\ -. C = D ) /\ -. B = D ) /\ -. ( ( D - B ) / ( C - B ) ) e. RR ) ) $=
    ( cc wcel wa wceq wn cmin co cdiv cr wne cc0 clt wbr w3a simpr wi simpl syl id 3jca gtrirotate mpd gtriside ) AEFZBEFZGZCEFZGZDEFZGZABHZIZBCHZIZGZACHZIZGZCAJKZBAJKZLKZMFZIZGZGZCDNZADJKZCDJKZLKZMFZVMOPQZRZGZVPURCDHZIZGZBDHZIZGZDBJKZCBJKZLKZMFZIZGZVIVPSVQURCAHZIZGZBAHZIZGZABJKZWELKZMFZIZGZVPWITZVQVHWTVQVIVHVIVPUAZUNVHSUBVQUHUIUKRVHWTTVQUHUIUKVQVIUHXBVIUNUHUNVHUAZUNULUHULUMUAZULUJUHUJUKUAZUJUHUHUHUIUAZUHUCZUBZUBZUBZUBZUBZVQVIUIXBVIUNUIXCUNULUIXDULUJUIXEUHUISZUBZUBZUBZUBZVQVIUKXBVIUNUKXCUNULUKXDUJUKSZUBZUBZUBZUDABCUEUBUFVQUMWTXATZVQVIUMXBVIUNUMXCULUMSUBUBVQUHUMYBTZXLVQUKUHYCTZYAVQUIUKYDTXQBCADUGUBUFUFUFUFUF $.
$}
