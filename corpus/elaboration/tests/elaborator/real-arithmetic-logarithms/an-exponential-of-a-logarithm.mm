$( tests/elaborator/real-arithmetic-logarithms/an-exponential-of-a-logarithm, elaborated from tests/elaborator/real-arithmetic-logarithms.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.real-arithmetic-logarithms.an-exponential-of-a-logarithm $p |- ( exp ` ( log ` 5 ) ) = 5 $=
    ( c5 clog cfv ce wceq wtru c1 cmul co eqidd fveq2d cexp eqid oveq12i 5nn0 numexp1 eqtri eqtr4i a1i crp wcel cz cr 5re cc0 clt wbr 5pos elrpd 1z relogexp syl2anc eqtrd ax-1cn mulridi eqcomd cc relogcld recn syl exp1 cn0 1nn0 expcld mullid oveq12d wa jca mul4 eqtr4d reeflogd mptru ) ABCZDCZAEFVNAAFVNAAFVNVNAFVMVMDFVMGVMHIZVMFVMVOVOFVMVOVOFVMVMVOFAABFAJZKFVMAGLIZBCZVOFAVQBAVQEZFAAVQAMZVQVQAAAGGLVTGMZNZAOPZQZRZSZKZFATUAZGUBUAZVRVOEZFAAUCUAZFUDSZUEAUFUGZFUHSZUIZWIFUJSZAGUKZULZUMZUMFVOJUMFVOGVMGLIZHIZVOFVOGGHIZXAHIZXAFGXBVMXAHFXBGXBGEZFGUNUOZSZUPZFVMWTXAFWTVMFVMUQUAZWTVMEZFVMUCUAZXHFAWOURZVMUSZUTZVMVAZUTZUPZFXAWTFWTUQUAZXAWTEZFVMGXMGVBUAZFVCSZVDZWTVEZUTZUPZUMZVFZFXCXCXAFGUQUAZYGVGZYGXQVGZVGZXCXCEZFYHYIFYGYGYGFUNSZYLVHZFYGXQYLYAVHZVHZGGGWTVIZUTZFXBGXAWTHXFYCVFZUMZUMZYTVJUMFVMVOWSUPUMKFAWOVKUMVPUMVPVJVL $.
$}
