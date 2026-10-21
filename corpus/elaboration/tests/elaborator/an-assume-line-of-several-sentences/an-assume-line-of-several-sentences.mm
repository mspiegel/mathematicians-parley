$( tests/elaborator/an-assume-line-of-several-sentences/an-assume-line-of-several-sentences, elaborated from tests/elaborator/an-assume-line-of-several-sentences.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.an-assume-line-of-several-sentences.an-assume-line-of-several-sentences $p |- ( ( ( A e. RR /\ B e. RR ) /\ ( A = 1 /\ B = 2 ) ) -> ( A + B ) = 3 ) $=
    ( cr wcel wa c1 wceq c2 caddc co c3 simpr simpl syl oveq1d oveq2d eqtrd eqid oveq12i 1p2e3 eqtri eqtr4i a1i ) ACDZBCDZEZAFGZBHGZEZEZABIJZFHIJZKUJUKFBIJULUJAFBIUJUIUGUFUILZUGUHMNOUJBHFIUJUIUHUMUGUHLNPQULKGUJULKKULULKFFHHIFRHRSTUAKRUBUCQ $.
$}
