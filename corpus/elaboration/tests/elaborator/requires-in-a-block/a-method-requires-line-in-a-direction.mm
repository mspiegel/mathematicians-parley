$( tests/elaborator/requires-in-a-block/a-method-requires-line-in-a-direction, elaborated from tests/elaborator/requires-in-a-block.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.requires-in-a-block.a-method-requires-line-in-a-direction $p |- ( ( ( ( A e. RR /\ B e. RR ) /\ 0 <_ A ) /\ 0 <_ B ) -> ( A < B <-> ( A ^ 2 ) < ( B ^ 2 ) ) ) $=
    ( cr wcel wa cc0 cle wbr clt c2 cexp co simpr wb simpl id syl jca lt2sq mpbid mpbird impbida ) ACDZBCDZEZFAGHZEZFBGHZEZABIHZAJKLZBJKLZIHZUIUJEZUJUMUIUJMUNUCUFEZUDUHEZEZUJUMNZUNUOUPUNUCUFUNUIUCUIUJOZUIUGUCUGUHOZUGUEUCUEUFOZUEUCUCUCUDOZUCPZQZQZQZQUNUIUFUSUIUGUFUTUEUFMZQZQRUNUDUHUNUIUDUSUIUGUDUTUGUEUDVAUCUDMZQZQZQUNUIUHUSUGUHMZQRRABSZQTUIUMEZUJUMUIUMMVNUQURVNUOUPVNUCUFVNUIUCUIUMOZVFQVNUIUFVOVHQRVNUDUHVNUIUDVOVKQVNUIUHVOVLQRRVMQUAUB $.
$}
