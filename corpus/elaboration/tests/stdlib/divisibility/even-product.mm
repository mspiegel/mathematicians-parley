$( tests/stdlib/divisibility/even-product, elaborated from tests/stdlib/divisibility.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.divisibility.even-product $p |- ( ( ( A e. ZZ /\ 2 || A ) /\ B e. ZZ ) -> 2 || ( A x. B ) ) $=
    ( cz wcel c2 cdvds wbr wa cmul co simpl simpr syl w3a wi 2z a1i id 3jca dvdsmultr1 mpd ) ACDZEAFGZHZBCDZHZUCEABIJZFGZUFUDUCUDUEKZUBUCLMUFECDZUBUENUCUHOUFUJUBUEUJUFPQUFUDUBUIUDUBUBUBUCKUBRMMUDUELSEABTMUA $.
$}
