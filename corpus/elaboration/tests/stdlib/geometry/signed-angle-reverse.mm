$( tests/stdlib/geometry/signed-angle-reverse, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.signed-angle-reverse $p |- ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ -. A = B ) /\ -. C = B ) /\ -. ( ( A - B ) ang ( C - B ) ) = _pi ) -> ( ( C - B ) ang ( A - B ) ) = -u ( ( A - B ) ang ( C - B ) ) ) $=
    ( cc wcel wa wceq wn cmin co cang cpi wne w3a cneg simpl simpr syl neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid 3jca wi id gsangrev mpd ) ADEZBDEZFZCDEZFZABGZHZFZCBGZHZFZABIJZCBIJZKJZLGZHZFZABMZCBMZVFLMZNZVEVDKJZVFOZGZVIVJVKVLVIBAGZHZVJVIABVIVCUSVCVHPZVCUTUSUTVBPZUQUSQRRSVIVJVRVIVJUSVRVJUSTVIABUAUBVIURVQVIVQURVQURTVIBAUCUBUDUEUFUDUGVIBCGZHZVKVICBVIVCVBVSUTVBQRSVIVKWBVIVKVBWBVKVBTVICBUAUBVIVAWAVAWATVICBUCUBUEUFUDUGVILVFGZHZVLVIVFLVCVHQSVIVLWDVIVLVHWDVLVHTVIVFLUAUBVIVGWCVIWCVGWCVGTVILVFUCUBUDUEUFUDUGUHVIUMUNUPNVMVPUIVIUMUNUPVIVCUMVSVCUTUMVTUTUQUMUQUSPZUQUOUMUOUPPZUOUMUMUMUNPUMUJRRRRRVIVCUNVSVCUTUNVTUTUQUNWEUQUOUNWFUMUNQRRRRVIVCUPVSVCUTUPVTUTUQUPWEUOUPQRRRUHABCUKRUL $.
$}
