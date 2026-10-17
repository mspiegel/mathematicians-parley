$( proofs/hammack/weighted-binomial-sum/weighted-row-sum, elaborated from proofs/hammack/weighted-binomial-sum.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/hammack/weighted-binomial-sum/weighted-term.mm $]
$[ proofs/hammack/weighted-binomial-sum/binomial-row-sum.mm $]

${
  $d k r $.
  $d A k r $.
  proofs.hammack.weighted-binomial-sum.weighted-row-sum $p |- ( A e. NN0 -> sum_ k e. ( 1 ... ( A + 1 ) ) ( k x. ( ( A + 1 ) _C k ) ) = ( ( A + 1 ) x. ( 2 ^ A ) ) ) $=
    ( cn0 wcel c1 caddc co cfz cv cbc cmul csu cmin c2 cexp wa wceq wral simpl id syl simpr jca proofs.hammack.weighted-binomial-sum.weighted-term ralrimiva wi rsp com12 mpd sumeq2dv cfn fzfi a1i cc nn0cn ax-1cn addcld cz cn elfznn nnz 1z zsubcld bccl syl2anc fsummulc2 eqcomd eqtrd cc0 eqid oveq12i addlidi eqtri eqtr4i oveq1d sumeq1d vr 0z nn0z elfznn0 oveq2d fsumshft cbvsumv proofs.hammack.weighted-binomial-sum.binomial-row-sum ) ACDZEAEFGZHGZBIZWFWHJGZKGZBLZWFWGAWHEMGZJGZBLZKGZWFNAOGZKGWEWKWGWFWMKGZBLZWOWEWGWJWQBWEWHWGDZPZWJWQQZBWGRZXAWTWEXBWEWSSZWEXABWGWTWTXAWTWEWSWTWEWEXCWETZUAZWEWSUBZUCAWHUDUAUEUAWTWSXBXAUFXFXBWSXAXABWGUGUHUAUIUJWEWOWRWEWGWMWFBWGUKDWEEWFULUMWEAEWEWEAUNDXDAUOUAEUNDWEUPUMUQWTWMCDZWMUNDWTWEWLURDXGXEWTWHEWTWHUSDZWHURDZWTWSXHXFWHWFUTUAWHVAUAEURDZWTVBUMVCWLAVDVEWMUOUAVFVGVHWEWNWPWFKWEWNVIAHGZAWHJGZBLZWPWEWNVIEFGZWFHGZWMBLZXMWEXPWNWEXOWGWMBWEXNEWFHXNEQWEXNEEXNXNEVIVIEEFVIVJEVJZVKEUPVLVMXQVNUMVOVPVGWEXMXPWEXMXOAVQIZEMGZJGZVQLZXPWEXLXTBVQEVIAXJWEVBUMVIURDWEVRUMWEWEAURDXDAVSUAWEWHXKDZPZXLCDZXLUNDYCWEXIYDYCWEWEWEYBSXDUAYCWHCDZXIYCYBYEWEYBUBWHAVTUAWHVSUAWHAVDVEXLUOUAWHXSQZWHXSAJYFTWAWBYAXPQWEXOXTWMVQBXRWHQZXSWLAJYGXRWHEMYGTVOWAWCUMVHVGVHWEWEXMWPQXDABWDUAVHWAVH $.
$}
