$( tests/elaborator/pairs-compared/points-apart-by-their-coordinates, elaborated from tests/elaborator/pairs-compared.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.elaborator.pairs-compared.points-apart-by-their-coordinates $p |- ( ( ( ( A e. CC /\ B e. CC ) /\ A = ( 1 + ( _i x. 1 ) ) ) /\ B = ( 2 + ( _i x. 3 ) ) ) -> -. A = B ) $=
    ( cc wcel wa c1 ci cmul co caddc wceq c2 c3 wne wn cop cr clt wbr 1re a1i 1lt2 jca ltne syl necomd neneqd intnanrd wb ax-1cn opthg mtbird neqcomd df-ne eqcom bicomd notbid bitrd mpbid simpl simpr wi 2re 3re gptapart mpd mpbird ) ACDZBCDZEZAFGFHIZJIZKZEZBLGMHIZJIZKZEZABNZABKZOZVRVSFFPZLMPZNZVRWCWBKZOZWDVRWBWCVRWBWCKZFLKZFMKZEZVRWHWIVRFLVRLFVRFQDZFLRSZELFNVRWKWLWKVRTUAZWLVRUBUAUCFLUDUEUFUGUHVRFCDZWNEWGWJUIVRWNWNWNVRUJUAZWOUCFFLMCCUKUEULUMVRWDWFVRWDWGOZWFWDWPUIVRWBWCUNUAVRWGWEVRWEWGWEWGUIVRWCWBUOUAUPUQURUPUSVRVMVQEZVSWDUIZVRVMVQVRVNVMVNVQUTVJVMVAUEVNVQVAUCVRWKWKEZLQDZMQDZEZEWQWRVBVRWSXBVRWKWKWMWMUCVRWTXAWTVRVCUAXAVRVDUAUCUCABFFLMVEUEVFVGVSWAUIVRABUNUAUS $.
$}
