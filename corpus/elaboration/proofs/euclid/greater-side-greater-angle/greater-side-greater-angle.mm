$( proofs/euclid/greater-side-greater-angle/greater-side-greater-angle, elaborated from proofs/euclid/greater-side-greater-angle.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]
$[ stdlib/geometry/greater-side-greater-angle.mm $]

${
  proofs.euclid.greater-side-greater-angle.greater-side-greater-angle $p |- ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ ( ( ( -. A = B /\ -. B = C ) /\ -. A = C ) /\ -. ( ( C - A ) / ( B - A ) ) e. RR ) ) /\ ( abs ` ( C - B ) ) < ( abs ` ( C - A ) ) ) -> ( abs ` ( ( C - A ) ang ( B - A ) ) ) < ( abs ` ( ( C - B ) ang ( A - B ) ) ) ) $=
    ( cc wcel wa wceq wn cmin co cdiv cr cabs cfv clt wbr cang simpl simpr syl jca id w3a wi 3jca gtriswap mpd gtrirotate stdlib.geometry.greater-side-greater-angle ) ADEZBDEZFZCDEZFZABGZHZBCGZHZFZACGZHZFZCAIJZBAIJZKJZLEZHZFZFZCBIJZMNZVCMNZOPZFZUMUKFZUJFZCBGZHZBAGZHZFZCAGZHZFZACIJZBCIJZKJZLEZHZFZFZVMFVCVDQJMNVJABIJQJMNOPVNWKVMVNVPWJVNVOUJVNUMUKVNVIUMVIVMRZVIUNUMUNVHRZULUMSZTZTZVNVIUKWLVIUNUKWMUNULUKULUMRZUJUKSZTZTZTZUAVNVIUJWLVIUNUJWMUNULUJWQULUJUJUJUKRZUJUBZTZTZTZTZUAVNVAVRFZUPFZVDVCKJZLEZHZFZWJVNVHXMVNVIVHWLUNVHSTVNUJUKUMUCVHXMUDVNUJUKUMXGXAWPUEABCUFTUGVNUJUMUKUCXMWJUDVNUJUMUKXGWPXAUEACBUHTUGUAVIVMSUACBAUIT $.
$}
