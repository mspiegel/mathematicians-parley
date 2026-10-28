$( stdlib/sets/subset-antisymmetric, elaborated from corpus/stdlib/sets.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A t $.
  $d B t $.
  stdlib.sets.subset-antisymmetric $p |- ( ( ( ( A e. _V /\ B e. _V ) /\ A C_ B ) /\ B C_ A ) -> A = B ) $=
    ( cvv wcel wa wss vt cv wral wceq simpl simpr syl wb dfss3 a1i mpbid jca gext ) ACDZBCDZEZABFZEZBAFZEZGHZBDZGAIZUGADZGBIZEABJUFUIUKUFUCUIUFUDUCUDUEKUBUCLMUCUINUFGABOPQUFUEUKUDUELUEUKNUFGBAOPQRGABSM $.
$}
