$( tests/elaborator/primes-and-brackets/bracketed-formula, elaborated from tests/elaborator/primes-and-brackets.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A x $.
  tests.elaborator.primes-and-brackets.bracketed-formula $p |- ( ( A e. RR /\ A. x e. RR x <_ A ) -> A <_ A ) $=
    ( cr wcel cv cle wbr wral wa simpr wi simpl id syl wceq breq1d rspcv mpd ) BCDZAEZBFGZACHZIZUBBBFGZSUBJUCSUBUDKUCSSSUBLSMNUAUDABCTBOZTBBFUEMPQNR $.
$}
