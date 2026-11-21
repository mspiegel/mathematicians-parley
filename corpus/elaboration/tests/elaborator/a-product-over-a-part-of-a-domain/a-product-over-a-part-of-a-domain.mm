$( tests/elaborator/a-product-over-a-part-of-a-domain/a-product-over-a-part-of-a-domain, elaborated from tests/elaborator/a-product-over-a-part-of-a-domain.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d a m x $.
  $d A a m x $.
  $d B a m x $.
  $d C a m x $.
  tests.elaborator.a-product-over-a-part-of-a-domain.a-product-over-a-part-of-a-domain $p |- ( ( ( ( ( ( A e. ~P ZZ /\ B e. ~P A ) /\ B e. Fin ) /\ C : A --> ZZ ) /\ A. x e. B x e. ZZ ) /\ A. x e. B ( C ` x ) e. ZZ ) -> prod_ x e. B ( x x. ( C ` x ) ) = ( prod_ x e. B x x. prod_ x e. B ( C ` x ) ) ) $=
    ( cz cpw wcel wa cfn wf cv wral cfv va cmul co cprod wceq simpl simpr syl cc wi id eleq1d rspcv mpd zcn fveq2d fprodmul wb vm oveq12d cbvprodv eqeq1i oveq1i oveq2i eqtri eqeq2i bitri a1i mpbid ) BEFZGZCBFZGZHZCIGZHZBEDJZHZAKZEGZACLZHZVLDMZEGZACLZHZCNKZVTDMZOPZNQZCVTNQZCWANQZOPZRZCVLVPOPZAQZCVLAQZCVPAQZOPZRZVSCVTWANVSVOVHVOVRSZVOVKVHVKVNSVKVIVHVIVJSVGVHTUAUAUAVSVTCGZHZVTEGZVTUBGWPVNWQWPVSVNVSWOSZVSVOVNWNVKVNTUAUAWPWOVNWQUCVSWOTZVMWQAVTCVLVTRZVLVTEWTUDZUEUFUAUGVTUHUAWPWAEGZWAUBGWPVRXBWPVSVRWRVOVRTUAWPWOVRXBUCWSVQXBAVTCWTVPWAEWTVLVTDXAUIUEUFUAUGWAUHUAUJWGWMUKVSWGCULKZXCDMZOPZULQZCXCULQZCXDULQZOPZRZWMWGXFWFRXJWCXFWFCWBXENULVTXCRZVTXCWAXDOXKUDZXKVTXCDXLUIZUMUNUOWFXIXFWFXGWEOPXIWDXGWEOCVTXCNULXLUNUPWEXHXGOCWAXDNULXMUNUQURUSUTXJWIXIRWMXFWIXICXEWHULAXCVLRZXCVLXDVPOXNUDZXNXCVLDXOUIZUMUNUOXIWLWIXIWJXHOPWLXGWJXHOCXCVLULAXOUNUPXHWKWJOCXDVPULAXPUNUQURUSUTUTVAVB $.
$}
