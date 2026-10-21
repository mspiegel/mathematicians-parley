$( tests/stdlib/geometry/area-by-sine, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.area-by-sine $p |- ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ -. A = C ) /\ -. B = C ) -> ( ( ( 1 / 2 ) x. ( ( abs ` ( B - C ) ) x. ( abs ` ( A - C ) ) ) ) x. ( abs ` ( sin ` ( ( B - C ) ang ( A - C ) ) ) ) ) = ( ( ( 1 / 2 ) x. ( ( abs ` ( B - C ) ) x. ( abs ` ( A - C ) ) ) ) x. ( sin ` ( abs ` ( ( B - C ) ang ( A - C ) ) ) ) ) ) $=
    ( cc wcel wa wceq wn wne c1 c2 cdiv co cmin cabs cfv cmul cang csin simpl simpr syl neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid jca w3a wi id 3jca garea mpd ) ADEZBDEZFZCDEZFZACGZHZFZBCGZHZFZACIZBCIZFZJKLMZBCNMZOPZACNMZOPZQMZQMZVNVPRMZSPZOPZQMZVSVTOPZSPZQMZGZVIVJVKVICAGZHZVJVIACVIVFVEVFVHTZVCVEUAUBUCVIVJWIVIVJVEWIVJVEUDVIACUEUFVIVDWHVIWHVDWHVDUDVICAUGUFUHUIUJUHUKVICBGZHZVKVIBCVFVHUAUCVIVKWLVIVKVHWLVKVHUDVIBCUEUFVIVGWKVIWKVGWKVGUDVICBUGUFUHUIUJUHUKULVIUSUTVBUMVLWGUNVIUSUTVBVIVFUSWJVFVCUSVCVETZVCVAUSVAVBTZVAUSUSUSUTTUSUOUBUBUBUBVIVFUTWJVFVCUTWMVCVAUTWNUSUTUAUBUBUBVIVFVBWJVFVCVBWMVAVBUAUBUBUPABCUQUBUR $.
$}
