$( tests/stdlib/calculus/cauchy-inside-a-larger-domain, elaborated from tests/stdlib/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]
$[ stdlib/calculus/cauchy-mean-value.mm $]

${
  $d A c $.
  $d B c $.
  $d C c $.
  $d D c $.
  tests.stdlib.calculus.cauchy-inside-a-larger-domain $p |- ( ( ( ( ( ( ( ( ( A e. RR /\ B e. RR ) /\ A < B ) /\ C : RR --> RR ) /\ D : RR --> RR ) /\ ( C |` ( A [,] B ) ) e. ( ( A [,] B ) -cn-> RR ) ) /\ ( D |` ( A [,] B ) ) e. ( ( A [,] B ) -cn-> RR ) ) /\ ( A (,) B ) C_ dom ( RR _D C ) ) /\ ( A (,) B ) C_ dom ( RR _D D ) ) -> E. c e. ( A (,) B ) ( ( ( C ` B ) - ( C ` A ) ) x. ( ( RR _D D ) ` c ) ) = ( ( ( D ` B ) - ( D ` A ) ) x. ( ( RR _D C ) ` c ) ) ) $=
    ( cr wcel wa clt wbr wf cicc co cres ccncf cioo cdv cdm wss cpw cfv cmin cv cmul wceq wrex cvv reex a1i ssid jca gsspw syl simpl id simpr iccssre stdlib.calculus.cauchy-mean-value ) AFGZBFGZHZABIJZHZFFCKZHZFFDKZHZCABLMZNZVHFOMZGZHZDVHNZVJGZHZABPMZFCQMZRZSZHZVPFDQMZRZSZHZFFTZGZUSHZUTHZVBHZVHFSZHZVDHZVFHZVKHZVNHZVSHZWCHBCUAACUAUBMEUCZWAUAUDMBDUAADUAUBMWQVQUAUDMUEEVPUFWDWPWCWDWOVSWDWNVNWDWMVKWDWLVFWDWKVDWDWIWJWDWHVBWDWGUTWDWFUSWDFUGGZFFSZHWFWDWRWSWRWDUHUIWSWDFUJUIUKFFUGULUMWDVTUSVTWCUNZVTVOUSVOVSUNZVOVLUSVLVNUNZVLVGUSVGVKUNZVGVEUSVEVFUNZVEVCUSVCVDUNZVCVAUSVAVBUNZVAUSUSUSUTUNZUSUOZUMZUMZUMZUMZUMZUMZUMZUMZUKWDVTUTWTVTVOUTXAVOVLUTXBVLVGUTXCVGVEUTXDVEVCUTXEVCVAUTXFUSUTUPZUMZUMZUMZUMZUMZUMZUMZUKWDVTVBWTVTVOVBXAVOVLVBXBVLVGVBXCVGVEVBXDVEVCVBXEVAVBUPUMUMUMUMUMUMUKWDVAWJWDUSUTXPYDUKABUQUMUKWDVTVDWTVTVOVDXAVOVLVDXBVLVGVDXCVGVEVDXDVCVDUPUMUMUMUMUMUKWDVTVFWTVTVOVFXAVOVLVFXBVLVGVFXCVEVFUPUMUMUMUMUKWDVTVKWTVTVOVKXAVOVLVKXBVGVKUPUMUMUMUKWDVTVNWTVTVOVNXAVLVNUPUMUMUKWDVTVSWTVOVSUPUMUKVTWCUPUKFABCDEURUM $.
$}
