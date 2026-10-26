$( tests/elaborator/a-map-written-short/a-map-written-short-read-at-a-value, elaborated from tests/elaborator/a-map-written-short.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A y $.
  tests.elaborator.a-map-written-short.a-map-written-short-read-at-a-value $p |- ( ( A e. RR /\ ( ( y e. RR |-> ( y + 1 ) ) ` A ) = 3 ) -> ( A + 1 ) = 3 ) $=
    ( cr wcel cv c1 caddc co cmpt cfv c3 wceq wa simpr cvv eqid id oveq1d simpl syl ovex a1i fvmptd3 eqeq1d mpbid ) BCDZBACAEZFGHZIZJZKLZMZUKBFGHZKLUFUKNULUJUMKULABUHUMCUIOUIPUGBLZUGBFGUNQRULUFUFUFUKSUFQTUMODULBFGUAUBUCUDUE $.
$}
