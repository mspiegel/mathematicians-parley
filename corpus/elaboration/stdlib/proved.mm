$( stdlib/proved, built by parley build.

   What the library proves below the readable layer: facts this corpus
   needs, set.mm does not state, and the readable layer cannot. Each group
   stands in a block of its own. $)

$[ stdlib/definitions.mm $]

${
$( Geometry: what this corpus needs of the plane and set.mm does not
   state. Points are complex numbers, distance is the absolute value of a
   difference, and the angle is the constant definitions.mm introduces,
   so everything here is a theorem rather than an axiom: CC is a model
   and nothing in it has to be assumed.  GEOMETRY.md takes that
   decision and says what it costs. $)

$( `angval` reads a value of the angle by substituting for the two names
   `df-ang` binds, and asks that they be free of what is substituted. They
   appear in no statement here, only inside the proofs. The pairs are
   written one at a time because `$d x y A B` would also hold A and B
   apart, and the lemmas below are applied at terms that share names. $)
$d x y $.
$d x A $.  $d y A $.
$d x B $.  $d y B $.
$d x C $.  $d y C $.
$d x P $.  $d y P $.
$d x Q $.  $d y Q $.
$d x R $.  $d y R $.
$d x S $.  $d y S $.
$d x T $.  $d y T $.
$d x U $.  $d y U $.

  gtrirec $p |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) -> ( ( A / B ) e. RR -> ( B / A ) e. RR ) ) $=
    ( cc wcel cc0 wne wa cdiv co cr c1 wceq recdiv adantr simpr divne0 jca
    rereccl syl eqeltrrd ex )
    ACDZAEFZGZBCDZBEFZGZGZABHIZJDZBAHIZJDUHUJGZKUIHIZUKJUHUMUKLUJABMNULUJUIEFZGUMJDULUJUNUHUJOUHUNUJABPNQUIRSTUA $.

  gtriswap $p |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( ( ( -. A = B /\ -. B = C ) /\ -. A = C ) /\ -. ( ( C - A ) / ( B - A ) ) e. RR ) -> ( ( ( -. A = C /\ -. C = B ) /\ -. A = B ) /\ -. ( ( B - A ) / ( C - A ) ) e. RR ) ) ) $=
    ( cc wcel w3a wceq wn wa cmin co cdiv cr simpr simpld simprd neqned
    necomd neneqd jca31 cc0 wne wi simp2 adantr simp1 subcld subeq0ad
    necon3bid mpbird jca simp3 gtrirec syl con3d mpd ex )
    ADEZBDEZCDEZFZABGZHZBCGZHZIZACGZHZIZCAJKZBAJKZLKZMEZHZIZVHCBGZHZIZVCIZVKVJLKZMEZHZIVAVOIZVSWBWCVHVQVCWCVFVHWCVIVNVAVONZOZPZWCCBWCBCWCBCWCVCVEWCVFVHWEOZPQRSWCVCVEWGOZTWCVNWBWCVIVNWDPWCWAVMWCVKDEZVKUAUBZIZVJDEZVJUAUBZIZIWAVMUCWCWKWNWCWIWJWCBAVAUSVOURUSUTUDZUEZVAURVOURUSUTUFZUEZUGWCWJBAUBWCBAWCBAWCABWCABWHQRSQWCVKUABAWCBAWPWRUHUIUJUKWCWLWMWCCAVAUTVOURUSUTULZUEZWRUGWCWMCAUBWCCAWCCAWCACWCACWFQRSQWCVJUACAWCCAWTWRUHUIUJUKUKVKVJUMUNUOUPUKUQ $.

  gtricol $p |- ( ( ( A e. CC /\ B e. CC /\ C e. CC ) /\ ( ( A - B ) =/= 0 /\ ( C - B ) =/= 0 ) ) -> ( ( ( A - B ) / ( C - B ) ) e. RR -> ( ( C - A ) / ( B - A ) ) e. RR ) ) $=
    ( cc wcel w3a cmin co cc0 wne wa cdiv cr c1 cneg wceq simp1 adantr simp3
    subcld simp2 simpl adantl div2neg syl3anc negsubdi2 syl2anc oveq12d
    nnncan2 oveq1d jca divsubdir divid eqtrd eqtr3d 3eqtr3d 1re a1i simpr wi
    gtrirec syl mpd resubcl eqeltrd ex )
    ADEZBDEZCDEZFZABGHZIJZCBGHZIJZKZKZVKVMLHZMEZCAGHZBAGHZLHZMEVPVRKZWANVMVKLHZGHZMWBACGHZOZVKOZLHZWEVKLHZWAWDWBWEDEVKDEZVLWHWIPWBACVPVGVRVJVGVOVGVHVIQZRZRZVPVIVRVJVIVOVGVHVISZRZRZTWBABWMVPVHVRVJVHVOVGVHVIUAZRZRZTZVPVLVRVOVLVJVLVNUBZUCZRZWEVKUDUEWBWFVSWGVTLWBVGVIWFVSPWMWPACUFUGWBVGVHWGVTPWMWSABUFUGUHWBVKVMGHZVKLHZWIWDWBXDWEVKLWBVGVIVHXDWEPWMWPWSACBUIUEUJWBXEVKVKLHZWCGHZWDWBWJVMDEZWJVLKZXEXGPWTWBCBWPWSTZWBWJVLWTXCUKZVKVMVKULUEWBXFNWCGWBWJVLXFNPWTXCVKUMUGUJUNUOUPWBNMEZWCMEZWDMEXLWBUQURWBVRXMVPVRUSWBXIXHVNKZKVRXMUTWBXIXNXKWBXHVNXJVPVNVRVOVNVJVLVNUSUCRUKUKVKVMVAVBVCNWCVDUGVEVF $.

  gtrirotate $p |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( ( ( -. A = B /\ -. B = C ) /\ -. A = C ) /\ -. ( ( C - A ) / ( B - A ) ) e. RR ) -> ( ( ( -. B = C /\ -. C = A ) /\ -. B = A ) /\ -. ( ( A - B ) / ( C - B ) ) e. RR ) ) ) $=
    ( cc wcel w3a wceq wn wa cmin co cdiv cr simpr simpld simprd neqned
    necomd neneqd jca31 cc0 wne wi simpl simp1 adantr simp2 subeq0ad
    necon3bid mpbird simp3 jca gtricol syl con3d mpd ex )
    ADEZBDEZCDEZFZABGZHZBCGZHZIZACGZHZIZCAJKZBAJKZLKZMEZHZIZVECAGZHZIZBAGZHZIZABJKZCBJKZLKZMEZHZIVAVOIZWAWFWGVEVQVTWGVCVEWGVFVHWGVIVNVAVONZOZOZPZWGCAWGACWGACWGVFVHWIPQRSWGBAWGABWGABWGVCVEWJOZQZRSTWGVNWFWGVIVNWHPWGWEVMWGVAWBUAUBZWCUAUBZIZIWEVMUCWGVAWPVAVOUDWGWNWOWGWNABUBWMWGWBUAABWGABVAURVOURUSUTUEUFVAUSVOURUSUTUGZUFZUHUIUJWGWOCBUBWGCBWGCBWGBCWGBCWKQRSQWGWCUACBWGCBVAUTVOURUSUTUKUFWRUHUIUJULULABCUMUNUOUPULUQ $.

  gangval $p |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) -> ( A ang B ) = ( Im ` ( log ` ( B / A ) ) ) ) $=
    ( vx vy cang df-ang angval ) CDABECDFG $.

  gangrec $p |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) -> ( B ang A ) = ( Im ` ( log ` ( 1 / ( B / A ) ) ) ) ) $=
    ( cc wcel cc0 wne wa cang co cdiv clog cfv cim c1 wceq vx vy df-ang
    angval ancoms simpr simpl jca recdiv syl eqcomd fveq2d eqtrd )
    ACDZAEFZGZBCDZBEFZGZGZBAHIZABJIZKLZMLZNBAJIZJIZKLZMLUNUKUPUSOPQBAHPQRSTUOURVBMUOUQVAKUOVAUQUOUNUKGVAUQOUOUNUKUKUNUAUKUNUBUCBAUDUEUFUGUGUH $.

  gangsym $p |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) -> ( abs ` ( A ang B ) ) = ( abs ` ( B ang A ) ) ) $=
    ( cc wcel cc0 wne wa cdiv co clog cfv cim cabs c1 cang cneg crp wceq cpi
    simpr wb simpld simpl simprd divcl syl3anc adantr jca divne0 syl lognegb
    syl2anc mpbid fveq2d ax-1cn a1i divneg2 eqcomd rpreccl eqeltrrd reccld
    recne0d eqtr4d wn arginv cr logcld imcl recn absneg eqtrd pm2.61dan vx vy
    df-ang angval ancoms recdiv 3eqtr4d )
    ACDZAEFZGZBCDZBEFZGZGZBAHIZJKZLKZMKZNWGHIZJKZLKZMKZABOIZMKBAOIZMKWFWGPZQDZWJWNRWFWRGZWJSMKWNWSWISMWSWRWISRZWFWRTZWSWGCDZWGEFZWRWTUAWFXBWRWFWCVTWAXBWFWCWDWBWETZUBZWFVTWAWBWEUCZUBZWFVTWAXFUDZBAUEZUFZUGZWFXCWRWFWEWBGZXCWFWEWBXDXFUHZBAUIZUJZUGZWGUKULUMUNWSWMSMWSWKPZQDZWMSRZWSNWQHIZXQQWSXQXTWSNCDZXBXCXQXTRYAWSUOUPXKXPNWGUQUFURWSWRXTQDXAWQUSUJUTWSWKCDWKEFXRXSUAWSWGXKXPVAWSWGXKXPVBWKUKULUMUNVCWFWRVDZGZWNWJYCWNWIPZMKZWJYCWMYDMYCWGWFXBYBXJUGZWFXCYBXOUGZWFYBTVEUNYCWICDZYEWJRYCWIVFDZYHYCWHCDYIYCWGYFYGVGWHVHUJWIVIUJWIVJUJVKURVLWFWOWIMVMVNABOVMVNVOZVPUNWFWPWMMWFWPABHIZJKZLKZWMWEWBWPYMRVMVNBAOYJVPVQWFYLWLLWFYKWKJWFWKYKWFXLWKYKRXMBAVRUJURUNUNVKUNVS $.

  gangsym3 $p |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( -. A = B /\ -. C = B ) -> ( abs ` ( ( A - B ) ang ( C - B ) ) ) = ( abs ` ( ( C - B ) ang ( A - B ) ) ) ) ) $=
    ( cc wcel w3a wceq wn wa cmin co cang cabs cfv cc0 wne simp1 adantr simp2
    subcld simpl adantl neqned subeq0ad necon3bid mpbird jca simp3 simpr
    gangsym syl ex )
    ADEZBDEZCDEZFZABGZHZCBGZHZIZABJKZCBJKZLKZMNZVCVBLKZMNZGZUPVAIZVBDEZVBOPZIZVCDEZVCOPZIZIVHVIVLVOVIVJVKVIABUPUMVAUMUNUOQZRZUPUNVAUMUNUOSZRZTVIVKABPVIABVAURUPURUTUAUBUCVIVBOABVIABVQVSUDUEUFUGVIVMVNVICBUPUOVAUMUNUOUHZRZVSTVIVNCBPVICBVAUTUPURUTUIUBUCVIVCOCBVICBWAVSUDUEUFUGUGVBVCUJUKUL $.

  gcosabs $p |- ( A e. RR -> ( cos ` ( abs ` A ) ) = ( cos ` A ) ) $=
    ( cr wcel cabs cfv ccos wceq cc0 0re a1i id cle wbr wa absid fveq2d cneg
    absnid cc simpl recnd cosneg syl eqtrd lecasei )
    ABCZADEZFEZAFEZGHAHBCUFIJUFKUFHALMNUGAFAOPUFAHLMZNZUHAQZFEZUIUKUGULFARPUKASCUMUIGUKAUFUJTUAAUBUCUDUE $.

  gangrange $p |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) -> ( abs ` ( A ang B ) ) e. ( 0 [,] _pi ) ) $=
    ( cc wcel cc0 wne wa cang co cabs cfv cdiv clog cim cpi cicc gangval
    fveq2d cr cle wbr simpr simpld simpl simprd divcl syl3anc jca divne0 syl
    logcld imcld recnd abscl absge0 cneg pire renegcl ax-mp a1i clt logimcl
    syl2anc ltled wb absle mpbir2and w3a 0re elicc2 mpbir3and eqeltrd )
    ACDZAEFZGZBCDZBEFZGZGZABHIZJKBALIZMKZNKZJKZEOPIZVSVTWCJABQRVSWDWEDZWDSDZEWDTUAZWDOTUAZVSWCCDZWGVSWCVSWBVSWAVSVPVMVNWACDZVSVPVQVOVRUBZUCZVSVMVNVOVRUDZUCZVSVMVNWNUEZBAUFZUGZVSVRVOGZWAEFZVSVRVOWLWNUHZBAUIZUJZUKZULZUMZWCUNUJVSWJWHXFWCUOUJVSWIOUPZWCTUAZWCOTUAZVSXGWCXGSDZVSOSDZXJUQOURUSUTXEVSXGWCVAUAZXIVSWKWTXLXIGZWRXCWAVBZVCZUCVDVSXLXIXOUEVSWCSDXKWIXHXIGVEXEXKVSUQUTZWCOVFVCVGVSESDZXKWFWGWHWIVHVEXQVSVIUTXPEOWDVJVCVKVL $.

  gangbnd3 $p |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( -. A = B /\ -. C = B ) -> ( ( abs ` ( ( A - B ) ang ( C - B ) ) ) e. RR /\ 0 <_ ( abs ` ( ( A - B ) ang ( C - B ) ) ) ) ) ) $=
    ( cc wcel w3a wceq wn wa cmin co cang cabs cfv cr cc0 cle wbr cpi cicc
    wne simp1 adantr simp2 subcld simpl adantl neqned subeq0ad necon3bid
    mpbird jca simp3 simpr gangrange syl wb 0re a1i pire elicc2 syl2anc mpbid
    simp1d simp2d ex )
    ADEZBDEZCDEZFZABGZHZCBGZHZIZABJKZCBJKZLKZMNZOEZPVSQRZIVJVOIZVTWAWBVTWAVSSQRZWBVSPSTKZEZVTWAWCFZWBVPDEZVPPUAZIZVQDEZVQPUAZIZIZWEWBWIWLWBWGWHWBABVJVGVOVGVHVIUBZUCZVJVHVOVGVHVIUDZUCZUEZWBWHABUAZWBABVOVLVJVLVNUFZUGZUHZWBVPPABWBABWOWQUIZUJZUKZULZWBWJWKWBCBVJVIVOVGVHVIUMZUCZWQUEZWBWKCBUAZWBCBVOVNVJVLVNUNZUGZUHZWBVQPCBWBCBXHWQUIZUJZUKZULZULZVPVQUOZUPZWBPOEZSOEZWEWFUQZYAWBURUSZYBWBUTUSZPSVSVAZVBZVCZVDWBVTWAWCYHVEULVF $.

  glawcos $p |- ( ( ( A e. CC /\ B e. CC /\ C e. CC ) /\ ( -. A = B /\ -. C = B ) ) -> ( ( abs ` ( C - A ) ) ^ 2 ) = ( ( ( ( abs ` ( A - B ) ) ^ 2 ) + ( ( abs ` ( B - C ) ) ^ 2 ) ) - ( 2 x. ( ( ( abs ` ( A - B ) ) x. ( abs ` ( B - C ) ) ) x. ( cos ` ( abs ` ( ( A - B ) ang ( C - B ) ) ) ) ) ) ) ) $=
    ( cc wcel w3a wceq wn wa cmin co cabs cfv c2 cexp caddc cmul cang ccos
    wne simp3 adantr simp1 simp2 3jca simpr adantl neqned simpl jca vx vy
    df-ang eqid lawcos syl2anc abssub oveq1d oveq2d cr cdiv clog cim cc0
    subcld subeq0ad necon3bid mpbird gangval syl divcld divne0d logcld imcld
    eqeltrd gcosabs eqcomd oveq12d eqtrd )
    ADEZBDEZCDEZFZABGZHZCBGZHZIZIZCAJKZLMZNOKZABJKZLMZNOKZCBJKZLMZNOKZPKZNWNWQQKZWMWPRKZSMZQKZQKZJKZWOBCJKZLMZNOKZPKZNWNXGQKZXALMZSMZQKZQKZJKWIWBVTWAFCBTZABTZIWLXEGWIWBVTWAWCWBWHVTWAWBUAZUBZWCVTWHVTWAWBUCZUBZWCWAWHVTWAWBUDZUBZUEWIXOXPWICBWHWGWCWEWGUFZUGZUHZWIABWHWEWCWEWGUIZUGZUHZUJUKULCABRXAWNWQWKUKULUMWNUNWQUNWKUNXAUNUOUPWIWSXIXDXNJWIWRXHWOPWIWQXGNOWIWBWAWQXGGZXRYBCBUQZUPZURUSWIXCXMNQWIWTXJXBXLQWIWQXGWNQYKUSWIXLXBWIXAUTEXLXBGWIXAWPWMVAKZVBMZVCMZUTWIWMDEZWMVDTZIZWPDEZWPVDTZIZIXAYNGWIYQYTWIYOYPWIABXTYBVEZWIYPXPYHWIWMVDABWIABXTYBVFZVGZVHZUJWIYRYSWICBXRYBVEZWIYSXOYEWIWPVDCBWICBXRYBVFZVGZVHZUJUJWMWPVIVJWIYMWIYLWIWPWMUUEUUAUUDVKWIWPWMUUEUUAUUHUUDVLVMVNVOXAVPVJVQVRUSVRVS $.

  gcoscan $p |- ( ( ( X e. CC /\ Y e. CC /\ Z e. CC ) /\ ( K e. CC /\ K =/= 0 ) ) -> ( ( Z - ( 2 x. ( K x. X ) ) ) = ( Z - ( 2 x. ( K x. Y ) ) ) -> X = Y ) ) $=
    ( cc wcel w3a cc0 wne wa c2 cmul co cmin wceq wb simpl simp3 syl 2cn a1i
    simpr simpld simp1 mulcld simp2 subcan syl3anc biimpd 2ne0 jca mulcan
    sylibd )
    BEFZCEFZDEFZGZAEFZAHIZJZJZDKABLMZLMZNMZDKACLMZLMZNMZOZVBVEOZBCOZVAVHVCVFOZVIVAVHVKVAUPVCEFVFEFVHVKPVAUQUPUQUTQZUNUOUPRSVAKVBKEFZVATUAZVAABVAURUSUQUTUBZUCZVAUQUNVLUNUOUPUDZSZUEZUEVAKVEVNVAACVPVAUQUOVLUNUOUPUFZSZUEZUEDVCVFUGUHUIVAVBEFVEEFVMKHIZJVKVIPVSWBVAVMWCVNWCVAUJUAUKVBVEKULUHUMVAUNUOUTVIVJPVRWAVOBCAULUHUM $.

  gangeq $p |- ( ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) /\ ( ( C e. CC /\ C =/= 0 ) /\ ( D e. CC /\ D =/= 0 ) ) ) -> ( ( cos ` ( abs ` ( A ang B ) ) ) = ( cos ` ( abs ` ( C ang D ) ) ) -> ( abs ` ( A ang B ) ) = ( abs ` ( C ang D ) ) ) ) $=
    ( cc wcel cc0 wne wa cang co cabs cfv wceq ccos cpi cicc wb simpl
    gangrange syl simpr cos11 syl2anc biimprd )
    AEFZAGHZIZBEFZBGHZIZIZCEFZCGHZIZDEFZDGHZIZIZIZABJKZLMZCDJKZLMZNZVBOMZVDOMZNZUTVBGPQKZFZVDVIFZVEVHRUTULVJULUSSABTUAUTUSVKULUSUBCDTUAVBVDUCUDUE $.

  gsas $p |- ( ( ( P e. CC /\ Q e. CC /\ R e. CC ) /\ ( S e. CC /\ T e. CC /\ U e. CC ) ) -> ( ( ( ( -. P = Q /\ -. Q = R ) /\ -. P = R ) /\ -. ( ( R - P ) / ( Q - P ) ) e. RR ) -> ( ( ( ( -. S = T /\ -. T = U ) /\ -. S = U ) /\ -. ( ( U - S ) / ( T - S ) ) e. RR ) -> ( ( abs ` ( P - Q ) ) = ( abs ` ( S - T ) ) -> ( ( abs ` ( ( P - Q ) ang ( R - Q ) ) ) = ( abs ` ( ( S - T ) ang ( U - T ) ) ) -> ( ( abs ` ( Q - R ) ) = ( abs ` ( T - U ) ) -> ( ( ( ( ( ( abs ` ( P - Q ) ) = ( abs ` ( S - T ) ) /\ ( abs ` ( Q - R ) ) = ( abs ` ( T - U ) ) ) /\ ( abs ` ( R - P ) ) = ( abs ` ( U - S ) ) ) /\ ( abs ` ( ( P - Q ) ang ( R - Q ) ) ) = ( abs ` ( ( S - T ) ang ( U - T ) ) ) ) /\ ( abs ` ( ( Q - R ) ang ( P - R ) ) ) = ( abs ` ( ( T - U ) ang ( S - U ) ) ) ) /\ ( abs ` ( ( R - P ) ang ( Q - P ) ) ) = ( abs ` ( ( U - S ) ang ( T - S ) ) ) ) ) ) ) ) ) ) $=
    ( cc wcel w3a wa wceq wn cmin co cdiv cr cabs cfv cang wi simpr adantr c2
    cexp caddc cmul ccos oveq1d oveq12d fveq2d oveq2d simpl simp1 syl simp2
    simp3 3jca simpld simprd neqned necomd neneqd jca glawcos 3eqtr4d cc0 cle
    wbr wb subcld abscld absge0d sq11 syl2anc mpbid jca31 3eqtr3d eqcomd eqid
    a1i eqtrd wne cpi cicc subeq0ad necon3bid mpbird gangrange 0re pire
    elicc2 simp1d recnd coscl sqcld addcld mulcld absne0d mulne0 gcoscan mpd
    gangeq ex )
    AGHZBGHZCGHZIZDGHZEGHZFGHZIZJZABKZLZBCKZLZJZACKZLZJZCAMNZBAMNZONZPHZLZJZDEKZLZEFKZLZJZDFKZLZJZFDMNZEDMNZONZPHZLZJZABMNZQRZDEMNZQRZKZUUACBMNZSNZQRZUUCFEMNZSNZQRZKZBCMNZQRZEFMNZQRZKZUUEUUQJZYAQRZYOQRZKZJZUULJZUUMACMNZSNZQRZUUODFMNZSNZQRZKZJZYAYBSNZQRZYOYPSNZQRZKZJZTZTZTZTXLYFJZYTUVTUWAYTJZUUEUVSUWBUUEJZUULUVRUWCUULJZUUQUVQUWDUUQJZUVKUVPUWEUVCUVJUWEUVBUULUWEUUEUUQUVAUWDUUEUUQUWCUUEUULUWBUUEUAZUBZUBZUWDUUQUAZUWEUUSUCUDNZUUTUCUDNZKZUVAUWEUUBUCUDNZUUNUCUDNZUENZUCUUBUUNUFNZUUHUGRZUFNZUFNZMNZUUDUCUDNZUUPUCUDNZUENZUCUUDUUPUFNZUUKUGRZUFNZUFNZMNZUWJUWKUWEUWOUXCUWSUXGMUWEUWMUXAUWNUXBUEUWEUUBUUDUCUDUWHUHZUWEUUNUUPUCUDUWIUHZUIZUWEUWRUXFUCUFUWEUWPUXDUWQUXEUFUWEUUBUUDUUNUUPUFUWHUWIUIZUWEUUHUUKUGUWDUULUUQUWCUULUAZUBZUJZUIZUKZUIZUWEXGXNCBKZLZJZJZUWJUWTKZUWEXGUYAUWEXDXEXFUWDXDUUQUWCXDUULUWBXDUUEUWAXDYTXLXDYFXLXGXDXGXKULZXDXEXFUMZUNZUBZUBZUBZUBZUBZUWDXEUUQUWCXEUULUWBXEUUEUWAXEYTXLXEYFXLXGXEUYDXDXEXFUOZUNZUBZUBZUBZUBZUBZUWDXFUUQUWCXFUULUWBXFUUEUWAXFYTXLXFYFXLXGXFUYDXDXEXFUPZUNZUBZUBZUBZUBZUBZUQZUWEXNUXTUWEXNXPUWEXQXSUWEXTYEUWDYFUUQUWCYFUULUWBYFUUEUWAYFYTXLYFUAZUBZUBZUBZUBZURZURZURZUWECBUWEBCUWEBCUWEXNXPVUMUSZUTZVAZVBZVCZVCZABCVDZUNZUWEXKYHFEKZLZJZJZUWKUXHKZUWEXKVVEUWEXHXIXJUWDXHUUQUWCXHUULUWBXHUUEUWAXHYTXLXHYFXLXKXHXGXKUAZXHXIXJUMZUNZUBZUBZUBZUBZUBZUWDXIUUQUWCXIUULUWBXIUUEUWAXIYTXLXIYFXLXKXIVVHXHXIXJUOZUNZUBZUBZUBZUBZUBZUWDXJUUQUWCXJUULUWBXJUUEUWAXJYTXLXJYFXLXKXJVVHXHXIXJUPZUNZUBZUBZUBZUBZUBZUQZUWEYHVVDUWEYHYJUWEYKYMUWEYNYSUWDYTUUQUWCYTUULUWBYTUUEUWAYTUAZUBZUBZUBZURZURZURZUWEFEUWEEFUWEEFUWEYHYJVWPUSZUTZVAZVBZVCZVCZDEFVDZUNZVEZUWEUUSPHZVFUUSVGVHZJZUUTPHZVFUUTVGVHZJZUWLUVAVIZUWEVXGVXHUWEYAUWECAVUEUYKVJZVKZUWEYAVXNVLZVCZUWEVXJVXKUWEYOUWEFDVWIVVOVJZVKZUWEYOVXRVLZVCZUUSUUTVMZVNZVOZVPUXNVCUWEUVFUGRZUVIUGRZKZUVJUWEUWNUWJUENZUCUUNUUSUFNZVYEUFNZUFNZMNZVYHUCVYIVYFUFNZUFNZMNZKZVYGUWEVYLUXBUWKUENZUCUUPUUTUFNZVYFUFNZUFNZMNZVYOUWEUWMUXAVYLWUAUXIUWEXEXFXDIZXPXSJZJUWMVYLKUWEWUBWUCUWEXEXFXDUYRVUEUYKUQUWEXPXSVUOUWEXQXSVULUSZVCVCBCAVDUNUWEXIXJXHIZYJYMJZJUXAWUAKUWEWUEWUFUWEXIXJXHVWBVWIVVOUQUWEYJYMVWRUWEYKYMVWOUSZVCVCEFDVDUNVQUWEVYQVYHVYTVYNMUWEUXBUWNUWKUWJUEUWEUUPUUNUCUDUWEUUNUUPUWIVRZUHUWEUUTUUSUCUDUWEUUSUUTVYDVRZUHZUIUWEVYSVYMUCUFUWEVYRVYIVYFVYFUFUWEUUPUUNUUTUUSUFWUHWUIUIVYFVYFKUWEVYFVSVTUIUKUIWAUWEVYEGHZVYFGHZVYHGHZIZVYIGHZVYIVFWBZJZJVYPVYGTUWEWUNWUQUWEWUKWULWUMUWEUVFGHWUKUWEUVFUWEUVFPHZVFUVFVGVHZUVFWCVGVHZUWEUVFVFWCWDNZHZWURWUSWUTIZUWEUUMGHZUUMVFWBZJZUVDGHZUVDVFWBZJZJZWVBUWEWVFWVIUWEWVDWVEUWEBCUYRVUEVJZUWEWVEBCWBZVUPUWEUUMVFBCUWEBCUYRVUEWEZWFZWGZVCZUWEWVGWVHUWEACUYKVUEVJZUWEWVHACWBZUWEACWUDUTZUWEUVDVFACUWEACUYKVUEWEZWFZWGZVCZVCZUUMUVDWHUNUWEVFPHZWCPHZWVBWVCVIWWEUWEWIVTZWWFUWEWJVTZVFWCUVFWKVNVOWLWMUVFWNUNUWEUVIGHWULUWEUVIUWEUVIPHZVFUVIVGVHZUVIWCVGVHZUWEUVIWVAHZWWIWWJWWKIZUWEUUOGHZUUOVFWBZJZUVGGHZUVGVFWBZJZJZWWLUWEWWPWWSUWEWWNWWOUWEEFVWBVWIVJZUWEWWOEFWBZVWSUWEUUOVFEFUWEEFVWBVWIWEZWFZWGZVCZUWEWWQWWRUWEDFVVOVWIVJZUWEWWRDFWBZUWEDFWUGUTZUWEUVGVFDFUWEDFVVOVWIWEZWFZWGZVCZVCZUUOUVGWHUNUWEWWEWWFWWLWWMVIWWGWWHVFWCUVIWKVNVOWLWMUVIWNUNUWEUWNUWJUWEUUNUWEUUNUWEUUMWVKVKZWMZWOUWEUUSUWEUUSVXOWMZWOZWPUQUWEWUOWUPUWEUUNUUSWXPWXQWQUWEUUNGHZUUNVFWBZJZUUSGHZUUSVFWBZJZJWUPUWEWYAWYDUWEWXSWXTWXPUWEUUMWVKWVOWRVCUWEWYBWYCWXQUWEYAVXNUWEYAVFWBZCAWBZUWECAUWECAUWEACWVSVAZVBZUTZUWEYAVFCAUWECAVUEUYKWEZWFZWGZWRZVCZVCUUNUUSWSUNVCVCVYIVYEVYFVYHWTUNXAUWEWVJWWTJVYGUVJTUWEWVJWWTWWDWXNVCUUMUVDUUOUVGXBUNXAVCUWEUVMUGRZUVOUGRZKZUVPUWEUWJUWMUENZUCUUSUUBUFNZWYOUFNZUFNZMNZWYRUCWYSWYPUFNZUFNZMNZKZWYQUWEXUBUWKUXAUENZUCUUTUUDUFNZWYPUFNZUFNZMNZXUEUWEUWNUXBXUBXUKUXJUWEXFXDXEIZCAKZLZBAKZLZJZJUWNXUBKUWEXULXUQUWEXFXDXEVUEUYKUYRUQUWEXUNXUPWYHUWEBAUWEABUWEABVUNUTZVAZVBZVCVCCABVDUNUWEXJXHXIIZFDKZLZEDKZLZJZJUXBXUKKUWEXVAXVFUWEXJXHXIVWIVVOVWBUQUWEXVCXVEUWEFDUWEDFWXIVAZVBZUWEEDUWEDEUWEDEVWQUTZVAZVBZVCVCFDEVDUNVQUWEXUGWYRXUJXUDMUWEUWKUWJUXAUWMUEWUJUWEUUDUUBUCUDUWEUUBUUDUWHVRZUHUIUWEXUIXUCUCUFUWEXUHWYSWYPWYPUFUWEUUTUUSUUDUUBUFWUIXVLUIWYPWYPKUWEWYPVSVTUIUKUIWAUWEWYOGHZWYPGHZWYRGHZIZWYSGHZWYSVFWBZJZJXUFWYQTUWEXVPXVSUWEXVMXVNXVOUWEUVMGHXVMUWEUVMUWEUVMPHZVFUVMVGVHZUVMWCVGVHZUWEUVMWVAHZXVTXWAXWBIZUWEYAGHZWYEJZYBGHZYBVFWBZJZJZXWCUWEXWFXWIUWEXWEWYEVXNWYLVCZUWEXWGXWHUWEBAUYRUYKVJZUWEXWHBAWBZUWEBAXUTUTZUWEYBVFBAUWEBAUYRUYKWEZWFZWGZVCZVCZYAYBWHUNUWEWWEWWFXWCXWDVIWWGWWHVFWCUVMWKVNVOWLWMUVMWNUNUWEUVOGHXVNUWEUVOUWEUVOPHZVFUVOVGVHZUVOWCVGVHZUWEUVOWVAHZXWTXXAXXBIZUWEYOGHZYOVFWBZJZYPGHZYPVFWBZJZJZXXCUWEXXGXXJUWEXXEXXFVXRUWEXXFFDWBZUWEFDXVHUTZUWEYOVFFDUWEFDVWIVVOWEZWFZWGZVCZUWEXXHXXIUWEEDVWBVVOVJZUWEXXIEDWBZUWEEDXVKUTZUWEYPVFEDUWEEDVWBVVOWEZWFZWGZVCZVCZYOYPWHUNUWEWWEWWFXXCXXDVIWWGWWHVFWCUVOWKVNVOWLWMUVOWNUNUWEUWJUWMWXRUWEUUBUWEUUBUWEUUAUWEABUYKUYRVJZVKZWMZWOWPUQUWEXVQXVRUWEUUSUUBWXQXYHWQUWEWYDUUBGHZUUBVFWBZJZJXVRUWEWYDXYKWYNUWEXYIXYJXYHUWEUUAXYFUWEUUAVFWBABWBXURUWEUUAVFABUWEABUYKUYRWEWFWGWRVCVCUUSUUBWSUNVCVCWYSWYOWYPWYRWTUNXAUWEXWJXXKJWYQUVPTUWEXWJXXKXWSXYEVCYAYBYOYPXBUNXAVCXCXCXCXCXC $.

$}

${
$( Series: the limit of a sequence as the page defines it, and the value
   of a series as the limit of its partial sums. $)
$d j k n $.
$d A j n x $.
$d B j x $.
$d ph j k n x $.

  ${
    climnnre.1 $e |- ( ( ph /\ n e. NN ) -> B e. RR ) $.
    climnnre.2 $e |- ( ph -> A e. RR ) $.
  climnnre $p |- ( ph -> ( ( n e. NN |-> B ) ~~> A <-> A. x e. RR ( 0 < x -> E. j e. NN A. n e. NN ( j <_ n -> ( abs ` ( B - A ) ) < x ) ) ) ) $=
    ( cn cmpt cli wbr cc0 cv clt cle cmin co cabs cfv wi wral cr wrex crp
    crli c1 nnuz cz wcel 1z a1i cc wa recnd eqid fmptd rlimclim ralrimiva wss
    nnssre rlim2 bitr3d ralrp bitrdi cuz wb rexuzre ax-mp uznnssnn ralss syl
    nnz anim12i eluz imbi1d ralbidva bitrd rexbiia bitr3i imbi2i ralbii )
    AFIDJZCKLZMBNZOLZENZFNZPLZDCQRZSTZWEOLZUAZFIUBZEUCUDZUAZBUCUBZWFWNEIUDZUAZBUCUBAWDWOBUEUBZWQAWCCUFLWDWTACWCUGIUHUGUIUJZAUKULAFIDUMWCAWHIUJZUNZDGUOZWCUPUQURABEFIDCADUMUJFIXDUSIUCUTAVAULACHUOVBVCWOBVDVEWPWSBUCWOWRWFWOWLFWGVFTZUBZEIUDZWRXAXGWOVGUKWLEFUGIUHVHVIXFWNEIWGIUJZXFWHXEUJZWLUAZFIUBZWNXHXEIUTXFXKVGWGVJWLFXEIVKVLXHXJWMFIXHXBUNZXIWIWLXLWGUIUJZWHUIUJZUNXIWIVGXHXMXBXNWGVMWHVMVNWGWHVOVLVPVQVRVSVTWAWBVE $.
  $}

  ${
    sersumlim.1 $e |- ( ( ph /\ k e. NN ) -> A e. RR ) $.
    sersumlim.2 $e |- ( ph -> ( n e. NN |-> sum_ k e. ( 1 ... n ) A ) ~~> B ) $.
  sersumlim $p |- ( ph -> sum_ k e. ( ZZ>= ` 1 ) A = B ) $=
    ( c1 cuz cfv csu cn cv cfz co cmpt cli wbr wa wceq vj eqid cz wcel 1z a1i
    cdm climrel releldmi syl cr cc simpl simpr nnuz eleqtrrdi jca recn cvv
    oveq2 sumeq1 sumex fvmptd3 isumclim3 climuni eqcomd )
    ACHIJZBDKZAELHEMZNOZBDKZPZCQRZVLVHQRZSCVHTAVMVNGABUADVLHVGVGUBHUCUDAUEUFAVMVLQUGUDGVLCQUHUIUJADMZVGUDZSZBUKUDZBULUDVQAVOLUDZSVRVQAVSAVPUMVQVOVGLAVPUNUOUPUQFUJBURUJAUAMZVGUDZSZEVTVKHVTNOZBDKZLVLUSVLUBVIVTTVJWCTVKWDTVIVTHNUTVJWCBDVAUJWBVTVGLAWAUNUOUPWDUSUDWBWCBDVBUFVCVDUQCVHVLVEUJVF $.
  $}

$}

${
$( Functions: images, inverses, and a bijection from one-to-one and
   onto. $)
$d x y A $.
$d x y B $.
$d x y F $.
$d x D $.
$d x S $.

  gfvelima $p |- ( ( F : A --> B /\ S C_ A ) -> ( D e. ( F " S ) <-> E. x e. S D = ( F ` x ) ) ) $=
    ( wf wss wa cima wcel cv cfv wceq wrex wfn wb ffn fvelimab sylan eqcom
    rexbii bitrdi )
    BCFGZEBHZIDFEJZKZALZFMZDNZAEOZDUINZAEOUDFBPUEUGUKQBCFRABEDFSTUJULAEUIDUAUBUC $.

  gf1cnvfv1 $p |- ( ( F : A -1-1-> B /\ C e. A ) -> ( `' F ` ( F ` C ) ) = C ) $=
    ( wf1 crn wf1o wcel cfv ccnv wceq f1f1orn f1ocnvfv1 sylan )
    ABDEADFZDGCAHCDIDJICKABDLAOCDMN $.

  gf1foen $p |- ( ( A e. V /\ F : A -1-1-> B /\ A. y e. B E. x e. A y = ( F ` x ) ) -> A ~~ B ) $=
    ( wcel wf1 cv cfv wceq wrex wral w3a wf1o cen wbr simp1 wfo simp2 wf f1f
    syl simp3 wa wb dffo3 a1i mpbir2and df-f1o f1oeng syl2anc )
    CFGZCDEHZBIZAIZEJZKZACLZBDMZNZUMCDEOZCDPQUMUNUTRVAVBUNCDESZUMUNUTTZVAVCCDEUAZUTVAUNVEVDCDEUBUCUMUNUTUDVCVEUTUEUFVAABCDEUGUHUIVBUNVCUEUFVACDEUJUHUICDFEUKUL $.

  gfmpt $p |- ( A. x e. A C e. B <-> ( x e. A |-> C ) : A --> B ) $=
    ( cmpt eqid fmpt ) ABCDABDEZHFG $.

  gfnfvima $p |- ( ( F : A --> B /\ S C_ A /\ D e. S ) -> ( F ` D ) e. ( F " S ) ) $=
    ( wf wfn wss wcel cfv cima ffn fnfvima syl3an1 )
    ABEFEAGDAHCDICEJEDKIABELADECMN $.

$}

${
$( Sets: the parts of a set with a property, and a set counted by the
   equal parts it splits into. $)
$d x ps $.
$d x A $.
$d x B $.
$d v w y z K $.
$d v w y z X $.
$d v w y z M $.
$d v w y z ph $.
$d x y z $.

  gsspw $p |- ( ( B e. V /\ A C_ B ) -> A e. ~P B ) $=
    ( wcel cpw wss elpw2g biimpar ) BCDABEDABFABCGH $.

  ${
    gelrabpw.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
  gelrabpw $p |- ( B e. V -> ( A e. { x e. ~P B | ph } <-> ( A C_ B /\ ps ) ) ) $=
    ( cpw crab wcel wa wss elrab elpw2g anbi1d bitrid )
    DACEHZIJDQJZBKEFJZDELZBKABCDQGMSRTBDEFNOP $.
  $}

  ${
    gpartcnt.1 $e |- ( ph -> X e. Fin ) $.
    gpartcnt.2 $e |- ( ph -> U_ w e. K w = X ) $.
    gpartcnt.3 $e |- ( ph -> A. y e. K A. z e. K A. x e. ( y i^i z ) y = z ) $.
    gpartcnt.4 $e |- ( ph -> A. v e. K ( # ` v ) = M ) $.
    gpartcnt.5 $e |- ( ph -> M e. NN0 ) $.
  gpartcnt $p |- ( ph -> ( # ` X ) = ( ( # ` K ) x. M ) ) $=
    ( chash cfv csu cmul co cv ciun wceq id cbviunv eqtr3id fveq2d cpw cfn
    wcel wss pwfi sylib wa ssiun2 adantl adantr sseqtrd velpw sylibr ex ssrdv
    ssfi syl2anc cin c0 wo wral wdisj wne wi r19.3rzv biimprd com12 wn df-ne
    imbi1i pm4.64 orcom 3bitri biimpi syl ralimi disjor hashiun eqtr3d fveq2
    eqeq1d cbvralvw sumeq2 eqtrd cc nn0cnd fsumconst )
    AIOPZGHCQZGOPZHRSZAWNGCTZOPZCQZWOACGWRUAZOPWNWTAXAIOAXAEGETZUAZIECGXBWRXBWRUBZUCZUDZKUEZUFACGWRAIUGZUHUIZGXHUJZGUHUIZAIUHUIZXIJIUKZULZACGXHAWRGUIZWRXHUIZAXOUMZWRIUJZXPXQWRXAIXOWRXAUJZACGWRUNZUOZAXAIUBZXOXGUPZUQZCIURZUSZUTZVAZXHGVBZVCZXQXLXRWRUHUIAXLXOJUPYDIWRVBVCAWRDTZUBZWRYKVDZVEUBZVFZDGVGZCGVGZCGWRVHAYLBYMVGZDGVGZCGVGYQLYSYPCGYRYODGYRYMVEVIZYLVJZYOYTYRYLYTYLYRYLBYMVKVLVMUUAYOUUAYNVNZYLVJYNYLVFYOYTUUBYLYMVEVOVPYNYLVQYNYLVRVSVTWAWBWBWAGWRYKCDYLUCWCUSWDWEAWSHUBZCGVGZWTWOUBAFTZOPZHUBZFGVGUUDMUUGUUCFCGUUEWRUBUUFWSHUUEWROWFWGWHULGWSHCWIWAWJAXKHWKUIWOWQUBYJAHNWLGHCWMVCWJ $.
  $}

  ${
    gpartsfin.1 $e |- ( ph -> X e. Fin ) $.
    gpartsfin.2 $e |- ( ph -> A. y e. K y C_ X ) $.
  gpartsfin $p |- ( ph -> K e. Fin ) $=
    ( cpw cfn wcel wss pwfi sylib cv wral wi rsp syl velpw biimpri syl6 ssrdv
    ssfi syl2anc )
    ADGZHIZCUDJCHIADHIUEEDKLABCUDABMZCIZUFDJZUFUDIZAUHBCNUGUHOFUHBCPQUIUHBDRSTUAUDCUBUC $.
  $}

  gcardeq $p |- ( ( A e. Fin /\ A ~~ B ) -> ( # ` A ) = ( # ` B ) ) $=
    ( cfn wcel cen wbr wa chash cfv wceq simpr wb simpl enfi syl mpbid hashen
    syl2anc mpbird )
    ACDZABEFZGZAHIZBHIZJZUATUAKZUBTBCDZUEUALTUAMZUBTUGUHUBUATUGLUFABNOPABQRS $.

$}

${
$( Groups: what is in a coset. $)
$d y z A $.
$d y z S $.
$d y z X $.
$d y z G $.

  gelcoset $p |- ( ( G e. Grp /\ S C_ ( Base ` G ) /\ A e. ( Base ` G ) ) -> ( X e. ( { A } ( LSSum ` G ) S ) <-> E. z e. S X = ( A ( +g ` G ) z ) ) ) $=
    ( cgrp wcel cbs cfv wss w3a csn clsm co vy cv cplusg wceq wrex cvv wb
    simp1 elex syl simp3 snssi simp2 3jca eqid lsmelvalx oveq1 eqeq2d rexbidv
    rexsng bitrd )
    DFGZCDHIZJZBUQGZKZEBLZCDMIZNZGZEOPZAPZDQIZNZRZACSZOVASZEBVFVGNZRZACSZUTDTGZVAUQJZURKVDVKUAUTVOVPURUTUPVOUPURUSUBDFUCUDUTUSVPUPURUSUEZBUQUFUDUPURUSUGUHOAUQVGVBVACDTEUQUIVGUIVBUIUJUDUTUSVKVNUAVQVJVNOBUQVEBRZVIVMACVRVHVLEVEBVFVGUKULUMUNUDUO $.

$}

${
$( Numbers: a remainder is less than its divisor. $)

  gzmodlt $p |- ( ( A e. ZZ /\ B e. NN ) -> ( A mod B ) < B ) $=
    ( cz wcel cr crp cmo co clt wbr cn zre nnrp modlt syl2an )
    ACDAEDBFDABGHBIJBKDALBMABNO $.

$}

${
$( Divisors: the sum of the divisors of a number, and of a prime's powers. $)
$d k p B $.
$d k N $.
$d k P $.

  g1sgmval $p |- ( B e. NN -> ( 1 sigma B ) = sum_ k e. { p e. NN | p || B } k ) $=
    ( cn wcel c1 csgm co cv cdvds wbr crab cexp csu cz wceq 1z sgmval2 mpan
    wa cc simpr elrabi syl nncn exp1 sumeq2dv eqtrd )
    ADEZFAGHZCIZAJKZCDLZBIZFMHZBNZUMUNBNFOEUIUJUPPQFABCRSUIUMUOUNBUIUNUMEZTZUNUAEZUOUNPURUNDEZUSURUQUTUIUQUBULCUNDUCUDUNUEUDUNUFUDUGUH $.

  g1sgmppw $p |- ( ( P e. Prime /\ N e. NN0 ) -> ( 1 sigma ( P ^ N ) ) = sum_ k e. ( 0 ... N ) ( P ^ k ) ) $=
    ( cprime wcel cn0 wa c1 cexp co csgm cc0 cfz ccxp cv csu cc wceq ax-1cn
    sgmppw mp3an1 cn simpl prmnn syl nncn cxp1 oveq1d adantr sumeq2dv eqtrd )
    ADEZCFEZGZHACIJZKJZLCMJZAHNJZBOZIJZBPZUQAUSIJZBPHQEULUMUPVARSHABCTUAUNUQUTVBBUNUTVBRUSUQEUNURAUSIUNAQEZURARUNAUBEZVCUNULVDULUMUCAUDUEAUFUEAUGUEUHUIUJUK $.

$}

${
$( Powers: the exponents of 2, 3 and 5 in 2^a 3^b 5^c are a, b and c. $)

  ${
    gpcoth.1 $e |- ( ph -> P e. Prime ) $.
    gpcoth.2 $e |- ( ph -> Q e. Prime ) $.
    gpcoth.3 $e |- ( ph -> P =/= Q ) $.
    gpcoth.4 $e |- ( ph -> N e. NN0 ) $.
  gpcoth $p |- ( ph -> ( P pCnt ( Q ^ N ) ) = 0 ) $=
    ( cexp co cpc cmul cc0 cprime wcel cq wne wa cz wceq cn prmnn syl nnzd zq
    nnne0d jca nn0zd pcexp syl3anc cdvds wbr wn neneqd c2 cuz cfv wb prmuz2
    dvdsprm syl2anc mtbird pceq0 mpbird oveq2d nn0cnd mul01d 3eqtrd )
    ABCDIJZKJZDBCKJZLJZDMLJMABNOZCPOZCMQZRDSOVJVLTEAVNVOACSOVNACACNOZCUAOZFCUBZUCZUDCUEUCACVSUFUGADHUHCBDUIUJAVKMDLAVKMTZBCUKULZUMZAWABCTZABCGUNABUOUPUQZOZVPWAWCURAVMWEEBUSUCFCBUTVAVBAVMVQVTWBUREVSBCVCVAVDVEADADHVFVGVH $.
  $}

  ${
    gpcmul3.1 $e |- ( ph -> P e. Prime ) $.
    gpcmul3.2 $e |- ( ph -> X e. NN ) $.
    gpcmul3.3 $e |- ( ph -> Y e. NN ) $.
    gpcmul3.4 $e |- ( ph -> Z e. NN ) $.
  gpcmul3 $p |- ( ph -> ( P pCnt ( ( X x. Y ) x. Z ) ) = ( ( ( P pCnt X ) + ( P pCnt Y ) ) + ( P pCnt Z ) ) ) $=
    ( cmul co cpc caddc cprime wcel cz cc0 wne wa wceq nnmulcld nnzd nnne0d
    jca pcmul syl3anc oveq1d eqtrd )
    ABCDJKZEJKZLKZBUILKZBELKZMKZBCLKZBDLKZMKZUMMKABNOZUIPOZUIQRZSEPOZEQRZSUKUNTFAUSUTAUIACDGHUAZUBAUIVCUCUDAVAVBAEIUBAEIUCUDUIEBUEUFAULUQUMMAURCPOZCQRZSDPOZDQRZSULUQTFAVDVEACGUBACGUCUDAVFVGADHUBADHUCUDCDBUEUFUGUH $.
  $}

  ${
    gpc2.1 $e |- ( ph -> A e. NN0 ) $.
    gpc2.2 $e |- ( ph -> B e. NN0 ) $.
    gpc2.3 $e |- ( ph -> C e. NN0 ) $.
  gpc2 $p |- ( ph -> ( 2 pCnt ( ( ( 2 ^ A ) x. ( 3 ^ B ) ) x. ( 5 ^ C ) ) ) = A ) $=
    ( c2 cexp co c3 cmul c5 cpc caddc cc0 cprime wcel 2prm a1i cn 2nn
    nnexpcld 3nn 5nn gpcmul3 cn0 wceq pcidlem syl2anc 3prm wne 2re 2lt3
    ltneii gpcoth oveq12d 5prm 2lt5 nn0cnd cc 0cn addcld addridd eqtrd 3eqtrd
    )
    AHHBIJZKCIJZLJMDIJZLJNJHVGNJZHVHNJZOJZHVINJZOJBPOJZPOJZBAHVGVHVIHQRZASTZAHBHUARAUBTEUCAKCKUARAUDTFUCAMDMUARAUETGUCUFAVLVNVMPOAVJBVKPOAVPBUGRVJBUHVQEBHUIUJAHKCVQKQRAUKTHKULAHKUMUNUOTFUPUQAHMDVQMQRAURTHMULAHMUMUSUOTGUPUQAVOVNBAVNABPABEUTZPVARAVBTVCVDABVRVDVEVF $.
  $}

  ${
    gpc3.1 $e |- ( ph -> A e. NN0 ) $.
    gpc3.2 $e |- ( ph -> B e. NN0 ) $.
    gpc3.3 $e |- ( ph -> C e. NN0 ) $.
  gpc3 $p |- ( ph -> ( 3 pCnt ( ( ( 2 ^ A ) x. ( 3 ^ B ) ) x. ( 5 ^ C ) ) ) = B ) $=
    ( c3 c2 cexp co cmul c5 cpc caddc cc0 cprime wcel 3prm a1i cn 2nn
    nnexpcld 3nn 5nn gpcmul3 2prm wne 2re 2lt3 ltneii necomi gpcoth cn0 wceq
    pcidlem syl2anc oveq12d 5prm 3re 3lt5 cc 0cn nn0cnd addcld addridd
    addlidd eqtrd 3eqtrd )
    AHIBJKZHCJKZLKMDJKZLKNKHVJNKZHVKNKZOKZHVLNKZOKPCOKZPOKZCAHVJVKVLHQRZASTZAIBIUARAUBTEUCAHCHUARAUDTFUCAMDMUARAUETGUCUFAVOVQVPPOAVMPVNCOAHIBVTIQRAUGTHIUHAIHIHUIUJUKULTEUMAVSCUNRVNCUOVTFCHUPUQURAHMDVTMQRAUSTHMUHAHMUTVAUKTGUMURAVRVQCAVQAPCPVBRAVCTACFVDZVEVFACWAVGVHVI $.
  $}

  ${
    gpc5.1 $e |- ( ph -> A e. NN0 ) $.
    gpc5.2 $e |- ( ph -> B e. NN0 ) $.
    gpc5.3 $e |- ( ph -> C e. NN0 ) $.
  gpc5 $p |- ( ph -> ( 5 pCnt ( ( ( 2 ^ A ) x. ( 3 ^ B ) ) x. ( 5 ^ C ) ) ) = C ) $=
    ( c5 c2 cexp co c3 cmul cpc caddc cc0 cprime wcel 5prm a1i cn 2nn
    nnexpcld 3nn 5nn gpcmul3 2prm wne 2re 2lt5 ltneii necomi gpcoth 3prm 3re
    3lt5 oveq12d cn0 wceq pcidlem syl2anc 00id oveq1d nn0cnd addlidd eqtrd
    3eqtrd )
    AHIBJKZLCJKZMKHDJKZMKNKHVHNKZHVINKZOKZHVJNKZOKPPOKZDOKZDAHVHVIVJHQRZASTZAIBIUARAUBTEUCALCLUARAUDTFUCAHDHUARAUETGUCUFAVMVOVNDOAVKPVLPOAHIBVRIQRAUGTHIUHAIHIHUIUJUKULTEUMAHLCVRLQRAUNTHLUHALHLHUOUPUKULTFUMUQAVQDURRVNDUSVRGDHUTVAUQAVPPDOKDAVOPDOVOPUSAVBTVCADADGVDVEVFVG $.
  $}

  ${
    g235a.1 $e |- ( ph -> A e. NN0 ) $.
    g235a.2 $e |- ( ph -> B e. NN0 ) $.
    g235a.3 $e |- ( ph -> C e. NN0 ) $.
    g235a.4 $e |- ( ph -> D e. NN0 ) $.
    g235a.5 $e |- ( ph -> E e. NN0 ) $.
    g235a.6 $e |- ( ph -> F e. NN0 ) $.
    g235a.7 $e |- ( ph -> ( ( ( 2 ^ A ) x. ( 3 ^ B ) ) x. ( 5 ^ C ) ) = ( ( ( 2 ^ D ) x. ( 3 ^ E ) ) x. ( 5 ^ F ) ) ) $.
  g235a $p |- ( ph -> A = D ) $=
    ( c2 cexp co c3 cmul c5 cpc oveq2d gpc2 3eqtr3d )
    AOOBPQZRCPQZSQZTDPQZSQZUAQOOEPQZRFPQZSQZTGPQZSQZUAQBEAUIUNOUANUBABCDHIJUCAEFGKLMUCUD $.
  $}

  ${
    g235b.1 $e |- ( ph -> A e. NN0 ) $.
    g235b.2 $e |- ( ph -> B e. NN0 ) $.
    g235b.3 $e |- ( ph -> C e. NN0 ) $.
    g235b.4 $e |- ( ph -> D e. NN0 ) $.
    g235b.5 $e |- ( ph -> E e. NN0 ) $.
    g235b.6 $e |- ( ph -> F e. NN0 ) $.
    g235b.7 $e |- ( ph -> ( ( ( 2 ^ A ) x. ( 3 ^ B ) ) x. ( 5 ^ C ) ) = ( ( ( 2 ^ D ) x. ( 3 ^ E ) ) x. ( 5 ^ F ) ) ) $.
  g235b $p |- ( ph -> B = E ) $=
    ( c3 c2 cexp co cmul c5 cpc oveq2d gpc3 3eqtr3d )
    AOPBQRZOCQRZSRZTDQRZSRZUAROPEQRZOFQRZSRZTGQRZSRZUARCFAUIUNOUANUBABCDHIJUCAEFGKLMUCUD $.
  $}

  ${
    g235c.1 $e |- ( ph -> A e. NN0 ) $.
    g235c.2 $e |- ( ph -> B e. NN0 ) $.
    g235c.3 $e |- ( ph -> C e. NN0 ) $.
    g235c.4 $e |- ( ph -> D e. NN0 ) $.
    g235c.5 $e |- ( ph -> E e. NN0 ) $.
    g235c.6 $e |- ( ph -> F e. NN0 ) $.
    g235c.7 $e |- ( ph -> ( ( ( 2 ^ A ) x. ( 3 ^ B ) ) x. ( 5 ^ C ) ) = ( ( ( 2 ^ D ) x. ( 3 ^ E ) ) x. ( 5 ^ F ) ) ) $.
  g235c $p |- ( ph -> C = F ) $=
    ( c5 c2 cexp co c3 cmul cpc oveq2d gpc5 3eqtr3d )
    AOPBQRZSCQRZTRZODQRZTRZUAROPEQRZSFQRZTRZOGQRZTRZUARDGAUIUNOUANUBABCDHIJUCAEFGKLMUCUD $.
  $}

$}

${
$( Calculus: continuity and derivatives of a sum and of a line, as the
   page says them of functions named apart from their values. $)
$d x ph $.
$d x A $.
$d x B $.
$d x D $.
$d x F $.
$d x G $.
$d x H $.
$d x I $.
$d x M $.
$d x U $.
$d x V $.

  ${
    gdvdm.1 $e |- ( ph -> D = ( x e. I |-> E ) ) $.
    gdvdm.2 $e |- ( ( ph /\ x e. I ) -> E e. V ) $.
  gdvdm $p |- ( ph -> I C_ dom D ) $=
    ( cdm cmpt dmeqd wcel wral wceq ralrimiva dmmptg syl eqtrd eqcomd eqimssd
    ) AECIZAUAEAUABEDJZIZEACUBGKADFLZBEMUCENAUDBEHOBEDFPQRST $.
  $}

  ${
    gdvval.1 $e |- ( ph -> D = ( x e. I |-> E ) ) $.
    gdvval.2 $e |- ( ( ph /\ x e. I ) -> E e. V ) $.
  gdvval $p |- ( ph -> A. x e. I ( D ` x ) = E ) $=
    ( cv cfv wceq wcel wa cmpt adantr fveq1d simpr eqid fvmpt2 syl2anc eqtrd
    ralrimiva )
    ABIZCJZDKBEAUCELZMZUDUCBEDNZJZDUFUCCUGACUGKUEGOPUFUEDFLUHDKAUEQHBEDFUGUGRSTUAUB $.
  $}

  ${
    gdvsub.1 $e |- ( ph -> A e. RR ) $.
    gdvsub.2 $e |- ( ph -> B e. RR ) $.
    gdvsub.3 $e |- ( ph -> F : ( A [,] B ) --> CC ) $.
  gdvsub $p |- ( ph -> dom ( RR _D F ) C_ ( A (,) B ) ) $=
    ( cr cdv co cdm cicc cioo crn ctg cfv cnt ccnfld ctopn cc wss ax-resscn
    a1i wcel iccssre syl2anc eqid tgioo2 dvbssntr wceq iccntr sseqtrd )
    AHDIJKBCLJZMNZOPZQPZPZBCMJZAUMHDUORSPZHTUAAUBUCGABHUDZCHUDZUMHUAEFBCUEUFUSUSUGZUHVBUIAUTVAUQURUJEFBCUKUFUL $.
  $}

  ${
    gdvdmicc.1 $e |- ( ph -> A e. RR ) $.
    gdvdmicc.2 $e |- ( ph -> B e. RR ) $.
    gdvdmicc.3 $e |- ( ph -> F : ( A [,] B ) --> CC ) $.
    gdvdmicc.4 $e |- ( ph -> ( A (,) B ) C_ dom ( RR _D F ) ) $.
  gdvdmicc $p |- ( ph -> dom ( RR _D F ) = ( A (,) B ) ) $=
    ( cr cdv co cdm cioo gdvsub eqssd ) AIDJKLBCMKABCDEFGNHO $.
  $}

  ${
    grolle.1 $e |- ( ph -> A e. RR ) $.
    grolle.2 $e |- ( ph -> B e. RR ) $.
    grolle.3 $e |- ( ph -> A < B ) $.
    grolle.4 $e |- ( ph -> F e. ( ( A [,] B ) -cn-> RR ) ) $.
    grolle.5 $e |- ( ph -> ( A (,) B ) C_ dom ( RR _D F ) ) $.
    grolle.6 $e |- ( ph -> ( F ` A ) = ( F ` B ) ) $.
  grolle $p |- ( ph -> E. x e. ( A (,) B ) ( ( RR _D F ) ` x ) = 0 ) $=
    ( cicc co cr cc ccncf wcel wf cncff syl wss ax-resscn a1i fssd gdvdmicc
    rolle ) ABCDEFGHIACDEFGACDLMZNOEAEUGNPMQUGNERIUGNESTNOUAAUBUCUDJUEKUF $.
  $}

  ${
    gdvf.1 $e |- ( ph -> A e. RR ) $.
    gdvf.2 $e |- ( ph -> B e. RR ) $.
    gdvf.3 $e |- ( ph -> F : ( A [,] B ) --> RR ) $.
    gdvf.4 $e |- ( ph -> ( A (,) B ) C_ dom ( RR _D F ) ) $.
  gdvf $p |- ( ph -> ( RR _D F ) : ( A (,) B ) --> RR ) $=
    ( cr cdv co cdm wf cioo cicc wss wcel iccssre syl2anc dvfre cc ax-resscn
    a1i fssd gdvdmicc feq2d mpbid )
    AIDJKZLZIUHMZBCNKZIUHMABCOKZIDMULIPZUJGABIQCIQUMEFBCRSULDTSAUIUKIUHABCDEFAULIUADGIUAPAUBUCUDHUEUFUG $.
  $}

  ${
    gdvre.1 $e |- ( ph -> A e. RR ) $.
    gdvre.2 $e |- ( ph -> B e. RR ) $.
    gdvre.3 $e |- ( ph -> F : ( A [,] B ) --> RR ) $.
    gdvre.4 $e |- ( ph -> ( A (,) B ) C_ dom ( RR _D F ) ) $.
    gdvre.5 $e |- ( ph -> C e. ( A (,) B ) ) $.
  gdvre $p |- ( ph -> ( ( RR _D F ) ` C ) e. RR ) $=
    ( cioo co cr cdv gdvf ffvelcdmd ) ABCKLMDMENLABCEFGHIOJP $.
  $}

  ${
    gdvaddof.1 $e |- ( ph -> D C_ RR ) $.
    gdvaddof.2 $e |- ( ph -> H : D --> RR ) $.
    gdvaddof.3 $e |- ( ph -> F : D --> RR ) $.
    gdvaddof.4 $e |- ( ph -> G : D --> RR ) $.
    gdvaddof.5 $e |- ( ph -> A. x e. D ( H ` x ) = ( ( F ` x ) + ( G ` x ) ) ) $.
  gdvaddof $p |- ( ph -> H = ( F oF + G ) ) $=
    ( cv cfv caddc co cmpt cof wfn wceq cr ffnd dffn5 sylib r19.21bi
    mpteq2dva eqtrd cvv wcel reex a1i ssexd inidm wa eqidd offval eqtr4d )
    AFBCBLZDMZUQEMZNOZPZDENQOAFBCUQFMZPZVAAFCRFVCSACTFHUABCFUBUCABCVBUTAVBUTSBCKUDUEUFABCCURUSNCDEUGUGACTDIUAACTEJUAACTUGTUGUHZAUIUJZGUKZVFCULAUQCUHZUMZURUNVHUSUNUOUP $.
  $}

  ${
    gdvaddbr.1 $e |- ( ph -> D C_ RR ) $.
    gdvaddbr.2 $e |- ( ph -> F : D --> RR ) $.
    gdvaddbr.3 $e |- ( ph -> G : D --> RR ) $.
    gdvaddbr.4 $e |- ( ph -> C e. dom ( RR _D F ) ) $.
    gdvaddbr.5 $e |- ( ph -> C e. dom ( RR _D G ) ) $.
  gdvaddbr $p |- ( ph -> C ( RR _D ( F oF + G ) ) ( ( ( RR _D F ) ` C ) + ( ( RR _D G ) ` C ) ) ) $=
    ( cr ccnfld ctopn cfv cdv co cc wss ax-resscn a1i fssd cdm wcel wbr wfun
    wb wf dvf ffun ax-mp funfvbrb sylib eqid dvaddbr )
    ABKDELMNZBKDOPZNZBKEOPZNZCCACKQDGKQRZASTZUAFACKQEHVAUAFVAABUPUBZUCZBUQUPUDZIUPUEZVCVDUFVBQUPUGVEDUHVBQUPUIUJBUPUKUJULABURUBZUCZBUSURUDZJURUEZVGVHUFVFQURUGVIEUHVFQURUIUJBURUKUJULUOUMUN $.
  $}

  ${
    gdvadd.1 $e |- ( ph -> D C_ RR ) $.
    gdvadd.2 $e |- ( ph -> H : D --> RR ) $.
    gdvadd.3 $e |- ( ph -> F : D --> RR ) $.
    gdvadd.4 $e |- ( ph -> G : D --> RR ) $.
    gdvadd.5 $e |- ( ph -> A. x e. D ( H ` x ) = ( ( F ` x ) + ( G ` x ) ) ) $.
    gdvadd.6 $e |- ( ph -> U C_ dom ( RR _D F ) ) $.
    gdvadd.7 $e |- ( ph -> U C_ dom ( RR _D G ) ) $.
  gdvadd $p |- ( ph -> U C_ dom ( RR _D H ) ) $=
    ( cr cdv co cdm cv wcel wa wrel cfv caddc wbr reldv a1i cof wss adantr wf
    simpr sseldd gdvaddbr wceq gdvaddof oveq2d breqd mpbird releldm syl2anc
    ex ssrdv )
    ABDOGPQZRZABSZDTZVFVETZAVGUAZVDUBZVFVFOEPQZUCZVFOFPQZUCZUDQZVDUEZVHVJVIOGUFUGVIVPVFVOOEFUDUHZQZPQZUEVIVFCEFACOUIVGHUJACOEUKVGJUJACOFUKVGKUJVIDVKRZVFADVTUIVGMUJAVGULZUMVIDVMRZVFADWBUIVGNUJWAUMUNVIVDVSVFVOVIGVROPAGVRUOVGABCEFGHIJKLUPUJUQURUSVFVOVDUTVAVBVC $.
  $}

  ${
    gdvaddv.1 $e |- ( ph -> D C_ RR ) $.
    gdvaddv.2 $e |- ( ph -> H : D --> RR ) $.
    gdvaddv.3 $e |- ( ph -> F : D --> RR ) $.
    gdvaddv.4 $e |- ( ph -> G : D --> RR ) $.
    gdvaddv.5 $e |- ( ph -> A. x e. D ( H ` x ) = ( ( F ` x ) + ( G ` x ) ) ) $.
    gdvaddv.6 $e |- ( ph -> U C_ dom ( RR _D F ) ) $.
    gdvaddv.7 $e |- ( ph -> U C_ dom ( RR _D G ) ) $.
  gdvaddv $p |- ( ph -> A. x e. U ( ( RR _D H ) ` x ) = ( ( ( RR _D F ) ` x ) + ( ( RR _D G ) ` x ) ) ) $=
    ( cv cr cdv co cfv caddc wceq wcel wa wfun wbr cdm cc wf dvf ffun ax-mp
    a1i cof wss adantr simpr sseldd gdvaddbr gdvaddof oveq2d breqd mpbird
    funbrfv imp syl2anc ralrimiva )
    ABOZPGQRZSZVGPEQRZSZVGPFQRZSZTRZUAZBDAVGDUBZUCZVHUDZVGVNVHUEZVOVRVQVHUFZUGVHUHVRGUIVTUGVHUJUKULVQVSVGVNPEFTUMZRZQRZUEVQVGCEFACPUNVPHUOACPEUHVPJUOACPFUHVPKUOVQDVJUFZVGADWDUNVPMUOAVPUPZUQVQDVLUFZVGADWFUNVPNUOWEUQURVQVHWCVGVNVQGWBPQAGWBUAVPABCEFGHIJKLUSUOUTVAVBVRVSVOVGVNVHVCVDVEVF $.
  $}

  ${
    gdvlinres.1 $e |- ( ph -> D C_ RR ) $.
    gdvlinres.2 $e |- ( ph -> U C_ D ) $.
    gdvlinres.3 $e |- ( ph -> U e. ( topGen ` ran (,) ) ) $.
    gdvlinres.4 $e |- ( ph -> M e. RR ) $.
    gdvlinres.5 $e |- ( ph -> G : D --> RR ) $.
    gdvlinres.6 $e |- ( ph -> A. x e. D ( G ` x ) = ( M x. x ) ) $.
  gdvlinres $p |- ( ph -> ( ( RR _D G ) |` U ) = ( x e. U |-> M ) ) $=
    ( cr cdv co cres c1 cmul cmpt cv cioo crn ctg cfv cnt cc wss wf wa wceq
    ax-resscn a1i fssd jca sstrd ccnfld ctopn eqid tgioo2 dvres syl ctop wcel
    retop isopn3i syl2anc reseq2d eqtrd eqcomd wfn ffnd dffn5 sylib r19.21bi
    mpteq2dva reseq1d resmpt oveq2d cpr reelprrecn adantr simpr sseldd recnd
    ax-1cn dvmptid dvmptres dvmptcmul mulridd )
    AMENOZDPZBDFQROZSZBDFSAWKMBDFBTZROZSZNOZWMAWKMEDPZNOZWQAWSWKAWSWJDUAUBZUCUDZUEUDZUDZPZWKAMUFUGZCUFEUHZUIZCMUGZDMUGZUIZUIWSXDUJAXGXJAXEXFXEAUKULZACMUFEKXKUMUNAXHXIGADCMHGUOZUNUNCDMXAEUPUQUDZXMURZXMXNUSZUTVAAXCDWJAXAVBVCZDXAVCXCDUJXPAVDULIDXAVEVFVGVHVIAWRWPMNAWRBCWOSZDPZWPAEXQDAEBCWNEUDZSZXQAECVJEXTUJACMEKVKBCEVLVMABCXSWOAXSWOUJBCLVNVOVHVPADCUGXRWPUJHBCDWOVQVAVHVRVHABWNQFMUFDMMUFVSZVCZAVTULZAWNDVCZUIZWNYEDMWNAXIYDXLWAAYDWBWCWDQUFVCZYEWEULABWNQMXAXMUFMDYCAWNMVCZUIZWNAYGWBWDYFYHWEULABMYCWFXLXOXNIWGAFJWDZWHVHABDWLFYEFAFUFVCYDYIWAWIVOVH $.
  $}

  ${
    gdvlin.1 $e |- ( ph -> D C_ RR ) $.
    gdvlin.2 $e |- ( ph -> U C_ D ) $.
    gdvlin.3 $e |- ( ph -> U e. ( topGen ` ran (,) ) ) $.
    gdvlin.4 $e |- ( ph -> M e. RR ) $.
    gdvlin.5 $e |- ( ph -> G : D --> RR ) $.
    gdvlin.6 $e |- ( ph -> A. x e. D ( G ` x ) = ( M x. x ) ) $.
  gdvlin $p |- ( ph -> U C_ dom ( RR _D G ) ) $=
    ( cr cdv co cres cdm gdvlinres wcel cv adantr gdvdm cin wceq dmres a1i
    wss inss2 eqsstrd sstrd )
    ADMENOZDPZQZUKQZABULFDMABCDEFGHIJKLRAFMSBTDSJUAUBAUMDUNUCZUNUMUOUDAUKDUEUFUOUNUGADUNUHUFUIUJ $.
  $}

  ${
    gdvlinv.1 $e |- ( ph -> D C_ RR ) $.
    gdvlinv.2 $e |- ( ph -> U C_ D ) $.
    gdvlinv.3 $e |- ( ph -> U e. ( topGen ` ran (,) ) ) $.
    gdvlinv.4 $e |- ( ph -> M e. RR ) $.
    gdvlinv.5 $e |- ( ph -> G : D --> RR ) $.
    gdvlinv.6 $e |- ( ph -> A. x e. D ( G ` x ) = ( M x. x ) ) $.
  gdvlinv $p |- ( ph -> A. x e. U ( ( RR _D G ) ` x ) = M ) $=
    ( cv cr cdv co cfv wceq wcel wa cres simpr fvres syl gdvlinres adantr
    gdvval r19.21bi eqtr3d ralrimiva )
    ABMZNEOPZQZFRBDAUKDSZTZUKULDUAZQZUMFUOUNUQUMRAUNUBUKDULUCUDAUQFRBDABUPFDNABCDEFGHIJKLUEAFNSUNJUFUGUHUIUJ $.
  $}

  ${
    gcncflin.1 $e |- ( ph -> D C_ RR ) $.
    gcncflin.2 $e |- ( ph -> M e. RR ) $.
    gcncflin.3 $e |- ( ph -> G : D --> RR ) $.
    gcncflin.4 $e |- ( ph -> A. x e. D ( G ` x ) = ( M x. x ) ) $.
  gcncflin $p |- ( ph -> G e. ( D -cn-> RR ) ) $=
    ( cv cmul co cmpt cr ccncf cfv wfn wceq ffnd dffn5 sylib r19.21bi
    mpteq2dva eqtrd wcel wf feq1d mpbid cc wss wb ax-resscn a1i recnd sstrd
    ssid cncfmptc syl3anc cncfmptid syl2anc mulcncf cncfcdm mpbird eqeltrd )
    ADBCEBJZKLZMZCNOLZADBCVEDPZMZVGADCQZDVJRZACNDHSZBCDTZUAZABCVIVFAVIVFRZBCIUBZUCZUDZAVGVHUEZCNVGUFZACNDUFWAHACNDVGVSUGUHANUIUJZVGCUIOLZUEVTWAUKWBAULUMZABEVECAEUIUECUIUJZUIUIUJZBCEMWCUEAEGUNACNUIFWDUOZWFAUIUPZUMZBECUIUQURAWEWFBCVEMWCUEWGWIBCUIUSUTVACUINVGVBUTVCVD $.
  $}

  ${
    gcncfadd.1 $e |- ( ph -> D C_ RR ) $.
    gcncfadd.2 $e |- ( ph -> H : D --> RR ) $.
    gcncfadd.3 $e |- ( ph -> F : D --> RR ) $.
    gcncfadd.4 $e |- ( ph -> G : D --> RR ) $.
    gcncfadd.5 $e |- ( ph -> A. x e. D ( H ` x ) = ( ( F ` x ) + ( G ` x ) ) ) $.
    gcncfadd.6 $e |- ( ph -> F e. ( D -cn-> RR ) ) $.
    gcncfadd.7 $e |- ( ph -> G e. ( D -cn-> RR ) ) $.
  gcncfadd $p |- ( ph -> H e. ( D -cn-> RR ) ) $=
    ( cv cfv caddc co cmpt cr ccncf wfn wceq ffnd dffn5 sylib r19.21bi
    mpteq2dva eqtrd wcel wf feq1d mpbid cc wss wb ax-resscn a1i ssid cncfss
    mp2an sseldd eqeltrrd addcncf cncfcdm syl2anc mpbird eqeltrd )
    AFBCBNZDOZVHEOZPQZRZCSTQZAFBCVHFOZRZVLAFCUAZFVOUBZACSFHUCZBCFUDZUEZABCVNVKAVNVKUBZBCKUFZUGZUHZAVLVMUIZCSVLUJZACSFUJWFHACSFVLWDUKULASUMUNZVLCUMTQZUIWEWFUOWGAUPUQABVIVJCADBCVIRZWHADCUADWIUBACSDIUCBCDUDUEAVMWHDVMWHUNZAWGUMUMUNZWJUPUMURZCSUMUSZUTZUQZLVAVBAEBCVJRZWHAECUAEWPUBACSEJUCBCEUDUEAVMWHEWOMVAVBVCCUMSVLVDVEVFVG $.
  $}

$}

