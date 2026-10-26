$( tests/elaborator/a-map-applied/a-value-assumed, elaborated from tests/elaborator/a-map-applied.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.a-map-applied.a-value-assumed $p |- ( ( ( A : RR --> RR /\ B e. RR ) /\ ( A ` B ) = 3 ) -> ( A ` B ) = 3 ) $=
    ( cr wf wcel wa cfv c3 wceq simpr ) CCADBCEFBAGHIJ $.
$}
