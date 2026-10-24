$( tests/notations/families/a-set-within-an-intersection, elaborated from tests/notations/families.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A m $.
  $d B m $.
  tests.notations.families.a-set-within-an-intersection $p |- ( ( ( A e. _V /\ B e. _V ) /\ A. m e. A B C_ m ) -> B C_ |^|_ m e. A m ) $=
    ( cvv wcel wa cv wss wral ciin simpr ssiin sylibr ) ADEZBDEZFZBCGZHZCAIZFSBCAQJHPSKCAQBLM $.
$}
