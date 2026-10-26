$( tests/elaborator/a-derivative-typed/a-derivative-typed, elaborated from tests/elaborator/a-derivative-typed.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.a-derivative-typed.a-derivative-typed $p |- ( ( A : RR --> RR /\ ( RR _D A ) : RR --> RR ) -> ( RR _D A ) : RR --> RR ) $=
    ( cr wf cdv co simpr ) BBACBBBADECF $.
$}
