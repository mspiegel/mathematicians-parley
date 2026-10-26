$( tests/elaborator/an-nth-derivative/an-nth-derivative-applied, elaborated from tests/elaborator/an-nth-derivative.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.an-nth-derivative.an-nth-derivative-applied $p |- ( ( ( ( A : RR --> RR /\ B e. NN ) /\ C e. RR ) /\ ( ( ( RR Dn A ) ` B ) ` C ) = 0 ) -> ( ( ( RR Dn A ) ` B ) ` C ) = 0 ) $=
    ( cr wf cn wcel wa cdvn co cfv cc0 wceq simpr ) DDAEBFGHCDGHCBDAIJKKLMN $.
$}
