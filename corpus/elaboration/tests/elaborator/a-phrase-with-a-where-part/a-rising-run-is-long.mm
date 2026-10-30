$( tests/elaborator/a-phrase-with-a-where-part/a-rising-run-is-long, elaborated from tests/elaborator/a-phrase-with-a-where-part.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d i j k m p q $.
  $d A i j k m p q $.
  $d B i j k m p q $.
  $d C i j k m p q $.
  $d D i j k m p q $.
  tests.elaborator.a-phrase-with-a-where-part.a-rising-run-is-long $p |- ( ( ( ( ( A e. NN /\ B e. NN ) /\ ( C : ( 1 ... A ) --> RR /\ C : ( 1 ... A ) -1-1-> RR ) ) /\ D e. ~P ( 1 ... A ) ) /\ ( B <_ ( # ` D ) /\ A. i e. D A. j e. D ( i < j -> ( C ` i ) < ( C ` j ) ) ) ) -> B <_ ( # ` D ) ) $=
    ( cn wcel wa c1 cfz co cr wf wf1 cpw chash cfv cle wbr cv clt wi wral vm vk simpr wb biid a1i mpbid vp vq wceq id breq2d fveq2d imbi12d cbvralvw ralbii simpl syl breq1d ralbidva bitri anbi2i simpld ) AGHZBGHZIZJAKLZMCNZVKMCOZIZIZDVKPZHZIZBDQRZSTZEUAZFUAZUBTZWACRZWBCRZUBTZUCZFDUDZEDUDZIZIZVTUEUAZUFUAZUBTZWLCRZWMCRZUBTZUCZUFDUDZUEDUDZWKWJVTWTIZWKWJWJVRWJUGWJWJUHWKWJUIUJUKWJXAUHWKWJVTULUAZUMUAZUBTZXBCRZXCCRZUBTZUCZUMDUDZULDUDZIXAWIXJVTWIWAXCUBTZWDXFUBTZUCZUMDUDZEDUDXJWHXNEDWGXMFUMDWBXCUNZWCXKWFXLXOWBXCWAUBXOUOZUPXOWEXFWDUBXOWBXCCXPUQUPURUSUTXNXIEULDWAXBUNZXMXHUMDXQXCDHZIZXKXDXLXGXSWAXBXCUBXSXQXQXQXRVAZXQUOZVBZVCXSWDXEXFUBXSWAXBCYBUQVCURVDUSVEVFXJWTVTXJXBWMUBTZXEWPUBTZUCZUFDUDZULDUDWTXIYFULDXHYEUMUFDXCWMUNZXDYCXGYDYGXCWMXBUBYGUOZUPYGXFWPXEUBYGXCWMCYHUQUPURUSUTYFWSULUEDXBWLUNZYEWRUFDYIWMDHZIZYCWNYDWQYKXBWLWMUBYKYIYIYIYJVAZYIUOZVBZVCYKXEWOWPUBYKXBWLCYNUQVCURVDUSVEVFVEUJUKVG $.
$}
