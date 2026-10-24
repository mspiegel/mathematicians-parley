$( tests/elaborator/a-named-value-of-a-function/a-named-value-of-a-function, elaborated from tests/elaborator/a-named-value-of-a-function.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A m $.
  $d B m $.
  $d C m $.
  tests.elaborator.a-named-value-of-a-function.a-named-value-of-a-function $p |- ( ( ( A e. NN /\ B : ( 1 ... A ) --> RR ) /\ C e. ( 1 ... A ) ) -> 0 <_ ( ( B ` C ) ^ 2 ) ) $=
    ( cn wcel c1 cfz co cr wf wa vm cv cfv wceq wex cc0 c2 cexp cle wbr cvv fvex a1i elisset syl simpr simpl ffvelcdm syl2anc eqeltrd sqge0 jca oveq1d breqtrd ex exlimdv mpd ) ADEZFAGHZIBJZKZCUTEZKZLMZCBNZOZLPZQVFRSHZTUAZVDVFUBEZVHVKVDCBUCUDLVFUBUEUFVDVGVJLVDVGVJVDVGKZQVERSHZVITVLVEIEZQVMTUAVLVEVFIVDVGUGZVLVAVCVFIEZVLVDVAVDVGUHZVDVBVAVBVCUHZUSVAUGZUFZUFZVLVDVCVQVBVCUGZUFZUTICBUIZUJZUKZVEULUFVLVEVFRSVLVGVNKVGVLVGVNVOWFUMVGVNUHUFUNUOUPUQUR $.
$}
