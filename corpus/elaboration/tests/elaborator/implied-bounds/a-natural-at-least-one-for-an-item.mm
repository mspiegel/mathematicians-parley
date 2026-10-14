$( tests/elaborator/implied-bounds/a-natural-at-least-one-for-an-item, elaborated from tests/elaborator/implied-bounds.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.implied-bounds.a-natural-at-least-one-for-an-item $p |- ( ( ( A e. NN /\ B e. RR ) /\ 0 < B ) -> ( B x. 1 ) <_ ( B x. A ) ) $=
    ( cn wcel cr wa cc0 clt wbr c1 cle cmul co simpl id syl nnge1 w3a wb 1re a1i nnre simpr jca 3jca lemul2 mpbid ) ACDZBEDZFZGBHIZFZJAKIZBJLMZBALMZKIZULUHUMULUJUHUJUKNZUJUHUHUHUINZUHOZPZPZAQPULJEDZAEDZUIUKFZRUMUPSULVBVCVDVBULTUAULUHVCVAAUBPULUIUKULUJUIUQUHUIUCPUJUKUCUDUEJABUFPUG $.
$}
