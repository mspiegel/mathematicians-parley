$( tests/elaborator/textbook-exercise-shapes-two/a-define-inside-a-case, elaborated from tests/elaborator/textbook-exercise-shapes-two.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A m $.
  tests.elaborator.textbook-exercise-shapes-two.a-define-inside-a-case $p |- ( ( A e. RR /\ ( A = 1 \/ A = 2 ) ) -> 0 < A ) $=
    ( cr wcel c1 wceq c2 wo wa cc0 clt wbr vm cv wex simpl id syl elisset 0lt1 a1i simpr eqcomd breqtrd eqeltrd jca ex exlimdv mpd 2pos mpjaodan ) ABCZADEZAFEZGZHZULIAJKZUMUOULHZLMZAEZLNZUPUQUKUTUQUOUKUOULOZUOUKUKUKUNOZUKPZQZQZLABRQUQUSUPLUQUSUPUQUSHZIURAJVFIAURJVFIDAJIDJKVFSTVFADVFUQULUQUSOZUOULUAQUBUCVFURAVFUSURBCZHZUSVFUSVHUQUSUAZVFURABVJVFUQUKVGVEQZUDZUEZUSVHOZQZUBUCVOUCUFUGUHUOUMHZIFAJIFJKVPUITVPAFUOUMUAUBUCUKUNUAUJ $.
$}
