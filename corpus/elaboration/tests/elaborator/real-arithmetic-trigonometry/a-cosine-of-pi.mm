$( tests/elaborator/real-arithmetic-trigonometry/a-cosine-of-pi, elaborated from tests/elaborator/real-arithmetic-trigonometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.real-arithmetic-trigonometry.a-cosine-of-pi $p |- ( cos ` _pi ) = -u 1 $=
    ( cpi ccos cfv c1 cneg wceq wtru cc0 caddc co cmul cexp cc wcel cr pire a1i recn syl exp1 eqcomd cn0 1nn0 expcld mullid eqtrd ax-1cn mulridi oveq12d wa jca mul4 eqtr4d eqidd mulcld addlid fveq2d 0cn cosppi cos0 negeqd mptru ) ABCZDEZFGVCVDVDGVCVDVDGVCHAIJZBCZVDGAVEBGADAKJZVEGADADLJZKJZVGGAVHVIGVHAGAMNZVHAFZGAONZVJVLGPQZARZSZATZSZUAZGVIVHGVHMNZVIVHFZGADVODUBNZGUCQZUDZVHUEZSZUAZUFZGVGDDKJZVIKJZVIGDWHAVIKGWHDWHDFZGDUGUHZQZUAZWGUIZGWIWIVIGDMNZWOUJZWOVSUJZUJZWIWIFZGWPWQGWOWOWOGUGQZWTUKZGWOVSWTWCUKZUKZDDDVHULZSZGWHDVIVHKWLWEUIZUFZUFZUMGVGVIVEXHGVEHVIIJZVIGHHAVIIGHUNWGUIGVIMNXIVIFGDVHWTWCUOVIUPSUFUMUFUQGVFHBCZEZVDGHMNZVFXKFXLGURQHUSSGXJDXJDFGUTQVAUFUFGVDUNZUFXMUMVB $.
$}
