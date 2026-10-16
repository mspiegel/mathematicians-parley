$( tests/elaborator/floor-in-a-bound/a-rounding-error-at-most-a-half, elaborated from tests/elaborator/floor-in-a-bound.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.floor-in-a-bound.a-rounding-error-at-most-a-half $p |- ( ( ( A e. RR /\ 0 <_ ( ( |_ ` ( A + ( 1 / 2 ) ) ) - A ) ) /\ ( ( |_ ` ( A + ( 1 / 2 ) ) ) - A ) <_ ( 1 / 2 ) ) -> ( abs ` ( ( |_ ` ( A + ( 1 / 2 ) ) ) - A ) ) <_ ( 1 / 2 ) ) $=
    ( cr wcel cc0 c1 c2 cdiv co caddc cfl cfv cmin cle wbr wa cabs wceq cz simpl id syl 1re a1i 2re cn wne 2nn nnne0 redivcld readdcld flcl zre resubcld simpr jca absid eqbrtrd ) ABCZDAEFGHZIHZJKZALHZMNZOZVBUSMNZOZVBPKZVBUSMVFVBBCZVCOVGVBQVFVHVCVFVAAVFVARCZVABCVFUTBCVIVFAUSVFVDURVDVESZVDURURURVCSZURTZUAZUAZVFEFEBCVFUBUCFBCVFUDUCVFFUECZFDUFVOVFUGUCFUHUAUIUJUTUKUAVAULUAVNUMVFVDVCVJURVCUNUAUOVBUPUAVDVEUNUQ $.
$}
