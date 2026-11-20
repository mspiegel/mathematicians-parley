$( tests/elaborator/unfolding-the-named-sentence/the-second-sentence-unfolded, elaborated from tests/elaborator/unfolding-the-named-sentence.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d m t x $.
  $d A m t x $.
  $d B m t x $.
  $d C m t x $.
  tests.elaborator.unfolding-the-named-sentence.the-second-sentence-unfolded $p |- ( ( ( ( A e. _V /\ B e. _V ) /\ C e. _V ) /\ ( A C_ B /\ A C_ C ) ) -> A. t e. A t e. C ) $=
    ( cvv wcel wa wss vx cv wral simpr syl wb dfss3 a1i mpbid vm wceq id eleq1d cbvralvw bitri ) BEFZCEFZGZDEFZGZBCHZBDHZGZGZIJZDFZIBKZAJZDFZABKZULUJUOULUKUJUHUKLUIUJLMUJUONULIBDOPQUOURNULUORJZDFZRBKURUNUTIRBUMUSSZUMUSDVATUAUBUTUQRABUSUPSZUSUPDVBTUAUBUCPQ $.
$}
