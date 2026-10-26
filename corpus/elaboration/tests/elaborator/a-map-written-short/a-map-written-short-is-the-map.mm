$( tests/elaborator/a-map-written-short/a-map-written-short-is-the-map, elaborated from tests/elaborator/a-map-written-short.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A y $.
  tests.elaborator.a-map-written-short.a-map-written-short-is-the-map $p |- ( ( A e. RR /\ ( ( y e. RR |-> ( y + 1 ) ) ` A ) = 3 ) -> ( ( y e. RR |-> ( y + 1 ) ) ` A ) = 3 ) $=
    ( cr wcel cv c1 caddc co cmpt cfv c3 wceq simpr ) BCDBACAEFGHIJKLM $.
$}
