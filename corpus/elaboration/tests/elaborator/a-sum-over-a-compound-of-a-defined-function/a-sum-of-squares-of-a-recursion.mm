$( tests/elaborator/a-sum-over-a-compound-of-a-defined-function/a-sum-of-squares-of-a-recursion, elaborated from tests/elaborator/a-sum-over-a-compound-of-a-defined-function.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d i j k m p q $.
  tests.elaborator.a-sum-over-a-compound-of-a-defined-function.a-sum-of-squares-of-a-recursion $p |- ( A. k e. NN0 ( ( ( i e. NN0 |-> ( seq 0 ( ( ( m e. _V |-> ( m + 1 ) ) o. 1st ) , ( NN0 X. { 1 } ) ) ` i ) ) ` k ) ^ 2 ) e. RR -> sum_ j e. ( 1 ... 1 ) ( ( ( i e. NN0 |-> ( seq 0 ( ( ( m e. _V |-> ( m + 1 ) ) o. 1st ) , ( NN0 X. { 1 } ) ) ` i ) ) ` j ) ^ 2 ) = ( ( ( i e. NN0 |-> ( seq 0 ( ( ( m e. _V |-> ( m + 1 ) ) o. 1st ) , ( NN0 X. { 1 } ) ) ` i ) ) ` 1 ) ^ 2 ) ) $=
    ( cv cn0 cvv c1 caddc co cmpt c1st ccom csn cxp cc0 cseq cfv c2 cexp cr wcel wral vp wceq wex cfz csu nn0ex a1i mptexg syl elisset wa cz cc 1z simpl id vq wb fveq2d oveq1d eleq1d cbvralvw simpr eqcomd fveq1d ralbidva bitrd mpbid wi 1nn0 rspcv mpd recn jca fsum1 sumeq2dv eqeq12d ex exlimdv ) CEZAFAEZDGDEZHIJZKZLMZFHNZOZPQZRZKZRZSTJZUAUBZCFUCZUDEZWMUEZUDUFZHHUGJZBEZWMRZSTJZBUHZHWMRZSTJZUEZWQWMGUBZWTWQFGUBZXIXJWQUIUJAFWLGUKULUDWMGUMULWQWSXHUDWQWSXHWQWSUNZXAXBWRRZSTJZBUHZHWRRZSTJZUEZXHXKHUOUBZXPUPUBZUNXQXKXRXSXRXKUQUJXKXPUAUBZXSXKWCWRRZSTJZUAUBZCFUCZXTXKWQYDXKWQWQWQWSURWQUSULXKWQUTEZWRRZSTJZUAUBZUTFUCZYDXKWQYEWMRZSTJZUAUBZUTFUCZYIWQYMVAXKWPYLCUTFWCYEUEZWOYKUAYNWNYJSTYNWCYEWMYNUSVBVCVDVEUJXKYLYHUTFXKYEFUBZUNZYKYGUAYPYJYFSTYPYEWMWRYPWRWMYPXKWSXKYOURWQWSVFZULVGVHVCVDVIVJYIYDVAXKYHYCUTCFYEWCUEZYGYBUAYRYFYASTYRYEWCWRYRUSVBVCVDVEUJVJVKXKHFUBZYDXTVLYSXKVMUJYCXTCHFWCHUEZYBXPUAYTYAXOSTYTWCHWRYTUSVBVCVDVNULVOXPVPULVQXMXPBHXBHUEZXLXOSTUUAXBHWRUUAUSVBVCVRULXKXNXEXPXGXKXAXMXDBXKXBXAUBZUNZXLXCSTUUCXBWRWMUUCXKWSXKUUBURYQULVHVCVSXKXOXFSTXKHWRWMYQVHVCVTVKWAWBVO $.
$}
