$( proofs/hammack/limit-unique/limit-unfolded, elaborated from proofs/hammack/limit-unique.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d k m x $.
  $d A k m x $.
  $d B k m x $.
  $d C k m x $.
  $d D k m x $.
  proofs.hammack.limit-unique.limit-unfolded $p |- ( ( ( ( ( A e. ~P RR /\ B : A --> RR ) /\ C e. RR ) /\ D e. RR ) /\ D e. ( B limCC C ) ) -> A. m e. RR ( 0 < m -> E. k e. RR ( 0 < k /\ A. x e. A ( ( -. x = C /\ ( abs ` ( x - C ) ) < k ) -> ( abs ` ( ( B ` x ) - D ) ) < m ) ) ) ) $=
    ( cr cpw wcel wf wa climc co cc0 cv clt wbr wne cmin cabs cfv wi wral wrex wceq wn simpr wss simpl id syl elpwi glimcre mpbid wb df-ne a1i anbi1d imbi1d ralbidv anbi2d rexbidva imbi2d ) BHIZJZBHCKZLZDHJZLZEHJZLZECDMNZJZLZOGPZQRZOFPZQRZAPZDSZVTDTNZUAUBZVRQRZLZVTCUBZETNZUAUBZVPQRZUCZABUDZLZFHUEZUCZGHUDZVQVSVTDUFZUGZWDLZWIUCZABUDZLZFHUEZUCZGHUDVOVNWOVLVNUHVOGFABDECVOVFBHUIVOVLVFVLVNUJZVLVJVFVJVKUJZVJVHVFVHVIUJZVHVFVFVFVGUJVFUKULULULULBHUMULVOVLVGXDVLVJVGXEVJVHVGXFVFVGUHULULULVOVLVIXDVLVJVIXEVHVIUHULULVOVLVKXDVJVKUHULUNUOVOWNXCGHVOWMXBVQVOWLXAFHVOVRHJZLZWKWTVSXHWJWSABXHWEWRWIXHWAWQWDWAWQUPXHVTDUQURUSUTVAVBVCVDVAUO $.
$}
