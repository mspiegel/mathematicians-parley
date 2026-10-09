$( tests/elaborator/large-arithmetic/remainder-of-a-small-number, elaborated from tests/elaborator/large-arithmetic.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.large-arithmetic.remainder-of-a-small-number $p |- ( 4 mod 7 ) = 4 $=
    ( c4 c7 cmo co wceq wtru eqid oveq12i cr wcel crp wa cc0 cle wbr clt 4re cn 7nn nnrp ax-mp pm3.2i 4nn0 nn0ge0i 4lt7 modid mp2an eqtri eqtr4i a1i mptru ) ABCDZAEZUMFULAAULULAAABBCAGZBGHAIJZBKJZLMANOZABPOZLUMUOUPQBRJUPSBTUAUBUQURAUCUDUEUBABUFUGUHUNUIUJUK $.
$}
