$( tests/elaborator/signed-divisibility/a-negative-number, elaborated from tests/elaborator/signed-divisibility.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.signed-divisibility.a-negative-number $p |- 2 || -u 8 $=
    ( c2 c8 cneg cdvds wbr wtru c4 cmul co cz wcel 2nn nnzi 4nn0 nn0zi dvdsmul1 mp2an 2t4e8 breqtri a1i wb 8nn0 dvdsnegb sylib eqidd breq12d mpbird mptru ) ABCZDEZFUJUJFABDEZUJUKFAAGHIZBDAJKZGJKAULDEALMZGNOAGPQRSTUMBJKUKUJUAUNBUBOABUCQUDFAAUIUIDFAUEFUIUEUFUGUH $.
$}
