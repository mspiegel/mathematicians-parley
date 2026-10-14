$( tests/elaborator/an-obtain-from-two-sentences/an-obtain-from-two-sentences, elaborated from tests/elaborator/an-obtain-from-two-sentences.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d m x y $.
  $d A m x y $.
  $d B m x y $.
  tests.elaborator.an-obtain-from-two-sentences.an-obtain-from-two-sentences $p |- ( ( ( A e. _V /\ B e. A ) /\ E. x e. A x = B ) -> E. y e. A y = B ) $=
    ( cvv wcel wa cv wceq wrex vm simpl simpr syl jca wb id eqeq1d cbvrexvw a1i mpbid rspcev ex rexlimdva mpd ) CEFZDCFZGZAHZDIZACJZGZKHZDIZKCJZBHZDIZBCJZULUKUOULUGUKGUKULUGUKULUHUGUHUKLUFUGMNUHUKMOUGUKMNUKUOPULUJUNAKCUIUMIZUIUMDUSQRSTUAULUNURKCULUMCFZGZUNURVAUNGZUTUNGURVBUTUNVBVAUTVAUNLULUTMNVAUNMOUQUNBUMCUPUMIZUPUMDVCQRUBNUCUDUE $.
$}
