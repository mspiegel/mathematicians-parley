$( tests/elaborator/a-negative-power-by-arithmetic/a-negative-power-in-a-system, elaborated from tests/elaborator/a-negative-power-by-arithmetic.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.a-negative-power-by-arithmetic.a-negative-power-in-a-system $p |- ( 1 ^ -u 1 ) e. NN $=
    ( c1 cneg cexp co cn wcel wtru 1nn a1i eqidd oveq12d cdiv cc ax-1cn cc0 wne ax-1ne0 cz 1z expnegd cmul wceq mulridi eqcomd oveq1d mulcld exp1 syl eqtrd oveq2d div1 wa jca mul4 mulrid eqtr4d wb mulne0d divmuleq syl2anc mpbird eleq1d mptru ) AABZCDZEFZGVFAEFZVGGHIGVEAEGVEVEAGAAVDVDCGAJGVDJKGVEAAACDZLDZAGAAAMFZGNIZAOPZGQIZARFGSITGVIAAUADZVNLDZAGAVNVHVNLGVNAVNAUBZGANUCZIZUDZGVHVNACDZVNGAVNACVSUEGVNMFZVTVNUBGAAVKVKUFZVNUGUHUIKGAVOVOGAVNVOVSGVOVNGVOVNALDZVNGVNAVNLGAVNVSUDUJGWAWCVNUBWBVNUKUHUIUDUIGVOVOUBZVNVNUADZWEUBZGWEWEGWEVNWEGWEWEVNGVNVNVNVNUAGVNWEVNGAVNAVNUAVSVSKZGWEWEVNGVJVJULZWHULZWFGWHWHGVJVJVKVKUMZWJUMZAAAAUNZUHZGVNAVNAUAVRGVJVPVKAUOZUHZKZUIZUIZWRKZWQUIZWTUPUDGWAWAULWAVNOPZULZXBULWDWFUQGWAWAWBWBUMGXBXBGWAXAWBGAAVKVKVMVMURZUMZXDUMVNVNVNVNUSUTVAUIUPUIUIVBVAVC $.
$}
