$( tests/elaborator/a-define-put-into-a-line/a-define-put-into-a-line, elaborated from tests/elaborator/a-define-put-into-a-line.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A m $.
  $d B m $.
  tests.elaborator.a-define-put-into-a-line.a-define-put-into-a-line $p |- ( ( A e. _V /\ B e. _V ) -> ( A i^i B ) C_ A ) $=
    ( cvv wcel wa vm cv cin wceq wex wss simpl id syl inex1g elisset inss1 a1i simpr eqcomd sseq1d mpbid ex exlimdv mpd ) ACDZBCDZEZFGZABHZIZFJZUJAKZUHUJCDZULUHUFUNUHUFUFUFUGLUFMNABCONFUJCPNUHUKUMFUHUKUMUHUKEZUIAKZUMUOUMUPUMUOABQRUOUJUIAUOUIUJUHUKSZTUAUBUOUIUJAUQUAUBUCUDUE $.
$}
