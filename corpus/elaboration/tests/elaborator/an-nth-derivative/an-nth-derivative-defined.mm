$( tests/elaborator/an-nth-derivative/an-nth-derivative-defined, elaborated from tests/elaborator/an-nth-derivative.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.an-nth-derivative.an-nth-derivative-defined $p |- ( ( ( ( A : RR --> RR /\ B e. NN ) /\ C e. RR ) /\ C e. dom ( ( RR Dn A ) ` B ) ) -> C e. dom ( ( RR Dn A ) ` B ) ) $=
    ( cr wf cn wcel wa cdvn co cfv cdm simpr ) DDAEBFGHCDGHCBDAIJKLGM $.
$}
