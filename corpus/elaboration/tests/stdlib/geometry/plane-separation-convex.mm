$( tests/stdlib/geometry/plane-separation-convex, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.plane-separation-convex $p |- ( ( ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. CC ) /\ E e. CC ) /\ -. A = B ) /\ 0 < ( ( Im ` ( ( C - A ) / ( B - A ) ) ) x. ( Im ` ( ( D - A ) / ( B - A ) ) ) ) ) /\ ( C =/= E /\ ( ( D - E ) / ( C - E ) ) e. RR /\ ( ( D - E ) / ( C - E ) ) < 0 ) ) -> 0 < ( ( Im ` ( ( E - A ) / ( B - A ) ) ) x. ( Im ` ( ( C - A ) / ( B - A ) ) ) ) ) $=
    ( cc wcel wa wceq wn cc0 cmin co cdiv cim cfv cmul clt wbr wne cr w3a simpl id syl simpr jca neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid gplanesepcvx ) AFGZBFGZHZCFGZHZDFGZHZEFGZHZABIZJZHZKCALMZBALMZNMZOPZDALMZVKNMZOPZQMZRSZHZCETZDELMZCELMZNMZUAGZWCKRSZUBZHZVFABTZHZVRHZWFHKEALMVKNMOPVMQMRSWGWJWFWGWIVRWGVFWHWGVDVEWGVBVCWGUTVAWGURUSWGVSURVSWFUCZVSVIURVIVRUCZVIVFURVFVHUCZVFVDURVDVEUCZVDVBURVBVCUCZVBUTURUTVAUCZUTURURURUSUCURUDUEUEUEUEUEUEUEWGVSUSWKVSVIUSWLVIVFUSWMVFVDUSWNVDVBUSWOVBUTUSWPURUSUFUEUEUEUEUEUEUGWGVSVAWKVSVIVAWLVIVFVAWMVFVDVAWNVDVBVAWOUTVAUFUEUEUEUEUEUGWGVSVCWKVSVIVCWLVIVFVCWMVFVDVCWNVBVCUFUEUEUEUEUGWGVSVEWKVSVIVEWLVIVFVEWMVDVEUFUEUEUEUGWGBAIZJZWHWGABWGVSVHWKVSVIVHWLVFVHUFUEUEUHWGWHWRWGWHVHWRWHVHUIWGABUJUKWGVGWQWGWQVGWQVGUIWGBAULUKUMUNUOUMUPUGWGVSVRWKVIVRUFUEUGVSWFUFUGABCDEUQUE $.
$}
