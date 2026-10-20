$( tests/elaborator/inspection-cases-of-a-range/one-of-a-named-range, elaborated from tests/elaborator/inspection-cases-of-a-range.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.inspection-cases-of-a-range.one-of-a-named-range $p |- ( ( ( A e. ~P ZZ /\ A = ( 3 ... 5 ) ) /\ B e. A ) -> ( ( B = 3 \/ B = 4 ) \/ B = 5 ) ) $=
    ( cz cpw wcel c3 c5 cfz co wceq wa csn c4 cun wo simpr simpl syl eqcomd c1 caddc 4p1e5 oveq2i cuz cfv cle wbr 3nn0 nn0zi 4nn0 clt 3lt4 3re 4re ltlei ax-mp eluz2 mpbir3an fzsuc eqtr3i 3p1e4 leidi fzsn sneqi uneq12i eqtri eqtrdi eleqtrd elun wi elsni a1i id orc syld olc jaod biimtrid mpd ) ACDZEZAFGHIZJZKZBAEZKZBFLZMLZNZGLZNZEZBFJZBMJZOZBGJZOZWFBAWKWDWEPWFAWBWKWFWBAWFAWBWFWDWCWDWEQWAWCPRSSWBFMHIZMTUAIZLZNZWKFWSHIZWBXAWSGFHUBUCMFUDUEZEZXBXAJXDFCEZMCEFMUFUGZFUHUIZMUJUIFMUKUGXFULFMUMUNUOUPFMUQURFMUSUPUTWRWIWTWJWRFFHIZFTUAIZLZNZWIFXIHIZWRXKXIMFHVAUCFXCEZXLXKJXMXEXEFFUFUGXGXGFUMVBFFUQURFFUSUPUTXHWGXJWHXEXHWGJXGFVCUPXIMVAVDVEVFWSGUBVDVEVFVGVHWLBWIEZBWJEZOWFWQBWIWJVIWFXNWQXOXNBWGEZBWHEZOWFWQBWGWHVIWFXPWQXQWFXPWMWQXPWMVJWFBFVKVLWMWQVJWFWMWOWQWMWMWOWMVMWMWNVNRWOWPVNZRVLVOWFXQWNWQXQWNVJWFBMVKVLWNWQVJWFWNWOWQWNWNWOWNVMWNWMVPRXRRVLVOVQVRWFXOWPWQXOWPVJWFBGVKVLWPWQVJWFWPWPWQWPVMWPWOVPRVLVOVQVRVS $.
$}
