$( tests/stdlib/counting/one-to-one-counted, elaborated from tests/stdlib/counting.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d f g i j k m $.
  $d A f g i j k m $.
  $d B f g i j k m $.
  tests.stdlib.counting.one-to-one-counted $p |- ( ( ( ( ( A e. _V /\ B e. _V ) /\ A e. Fin ) /\ B e. Fin ) /\ ( # ` A ) <_ ( # ` B ) ) -> ( # ` { g e. ( B ^m A ) | g : A -1-1-> B } ) = prod_ j e. ( 0 ... ( ( # ` A ) - 1 ) ) ( ( # ` B ) - j ) ) $=
    ( cvv wcel wa cfn chash cfv cle wbr vf cv wf1 cmap co crab cc0 c1 cmin cfz vk cprod wceq simpl simpr syl gf1cnt wb vi vm id f1eq1 cbvrabv fveq2i eqeq1i oveq2d cbvprodv eqeq2i bitri a1i mpbid ) AEFZBEFZGZAHFZGZBHFZGZAIJZBIJZKLZGZABMNZOZMBAPQZRZIJZSVKTUAQZUBQZVLUCNZUAQZUCUDZUEZABCNZOZCVQRZIJZWAVLDNZUAQZDUDZUEZVNMUCABVNVJVGVJVMUFZVJVHVGVHVIUFVFVGUGUHUHVNVJVIWNVHVIUGUHVJVMUGUIWEWMUJVNWEABUKNZOZUKVQRZIJZWAVLULNZUAQZULUDZUEZWMWEWRWDUEXBVSWRWDVRWQIVPWPMUKVQVOWOUEZXCVPWPUJXCUMABVOWOUNUHUOUPUQWDXAWRWAWCWTUCULWBWSUEZWBWSVLUAXDUMURUSUTVAXBWIXAUEWMWRWIXAWQWHIWPWGUKCVQWOWFUEZXEWPWGUJXEUMABWOWFUNUHUOUPUQXAWLWIWAWTWKULDWSWJUEZWSWJVLUAXFUMURUSUTVAVAVBVC $.
$}
