$( tests/stdlib/counting/card, elaborated from tests/stdlib/counting.proof by parley/elaborate.py.
   Everything is built except the statements below, which are
   taken as the readable lines state them: a closure method
   the elaborator does not expand, or a definition the
   database gives no target for.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

card.itm1 $a |- ( A e. _V -> ( B e. NN0 -> ( ( # ` A ) = B <-> { i e. NN | i <_ B } ~~ A ) ) ) $.

${
  $d A i $.
  $d B i $.
  card $p |- ( ( ( A e. _V /\ B e. NN0 ) /\ ( # ` A ) = B ) -> { i e. NN | i <_ B } ~~ A ) $=
    ( cvv wcel cn0 wa chash cfv wceq cv cle wbr cn crab cen simpr wb simpl syl wi id card.itm1 mpd mpbid ) ADEZBFEZGZAHIZBJZGZUJCKZBLMZCNOZAPMZUHUJQUKUGUJUORZUKUHUGUHUJSZUFUGQTUKUFUGUPUAUKUHUFUQUHUFUFUFUGSUFUBTTABCUCTUDUE $.
$}
