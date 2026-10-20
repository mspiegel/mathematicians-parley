$( tests/stdlib/numbers/triangle-inequality, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.triangle-inequality $p |- ( ( A e. RR /\ B e. RR ) -> ( abs ` ( A + B ) ) <_ ( ( abs ` A ) + ( abs ` B ) ) ) $=
    ( cr wcel wa cc caddc co cabs cfv cle wbr simpl id syl recn simpr jca abstri ) ACDZBCDZEZAFDZBFDZEABGHIJAIJBIJGHKLUBUCUDUBTUCUBTTTUAMTNOAPOUBUAUDTUAQBPORABSO $.
$}
