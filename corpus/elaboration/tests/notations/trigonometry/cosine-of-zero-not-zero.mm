$( tests/notations/trigonometry/cosine-of-zero-not-zero, elaborated from tests/notations/trigonometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.notations.trigonometry.cosine-of-zero-not-zero $p |- -. ( cos ` 0 ) = 0 $=
    ( cc0 ccos cfv wceq wn wtru wa c1 simpl cos0 a1i syl eqcomd simpr eqtrd cr wcel clt wbr wne 0re 0lt1 jca ltne neneqd pm2.21dd ex pm2.01d mptru ) ABCZADZEZFUKFUKULFUKGZHADULUMHUJAUMUJHUMFUJHDZFUKIUNFJKLMFUKNOUMHAUMAPQZAHRSZGHATUMUOUPUOUMUAKUPUMUBKUCAHUDLUEUFUGUHUI $.
$}
