$( tests/stdlib/geometry/angle, elaborated from tests/stdlib/geometry.proof by parley/elaborate.py.
   Everything is built except the statements below, which are
   taken as the readable lines state them: a closure method
   the elaborator does not expand, or a definition the
   database gives no target for.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

angle.itm1 $a |- ( A e. CC -> ( B e. CC -> ( C e. CC -> ( -. A = B -> ( -. C = B -> ( ( abs ` ( ( A - B ) ang ( C - B ) ) ) e. RR /\ 0 <_ ( abs ` ( ( A - B ) ang ( C - B ) ) ) ) ) ) ) ) ) $.

${
  angle $p |- ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ -. A = B ) /\ -. C = B ) -> ( ( abs ` ( ( A - B ) ang ( C - B ) ) ) e. RR /\ 0 <_ ( abs ` ( ( A - B ) ang ( C - B ) ) ) ) ) $=
    ( cc wcel wa wceq wn cmin co cang cabs cfv cr cc0 cle wbr simpr wi simpl syl id angle.itm1 mpd ) ADEZBDEZFZCDEZFZABGZHZFZCBGZHZFZUNABIJZCBIJZKJZLMZNEZOUSPQZFZULUNRUOUKUNVBSZUOULUKULUNTZUIUKRUAUOUHUKVCSZUOULUHVDULUIUHUIUKTZUGUHRUAUAUOUFUHVESZUOULUFVDULUIUFVFUIUGUFUGUHTZUEUFRUAUAUAUOUEUFVGSUOULUEVDULUIUEVFUIUGUEVHUGUEUEUEUFTUEUBUAUAUAUAABCUCUAUDUDUDUD $.
$}
