$( tests/notations/functions/a-bijection-is-onto, elaborated from tests/notations/functions.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.notations.functions.a-bijection-is-onto $p |- ( ( ( A e. _V /\ B e. _V ) /\ ( C : A --> B /\ C : A -1-1-onto-> B ) ) -> C : A -onto-> B ) $=
    ( cvv wcel wa wf wf1o wf1 wfo simpr syl wb df-f1o a1i mpbid ) ADEZBDEZFZABCGZABCHZFZFZABCIZABCJZFZUEUCUAUFUCUBUASUBKTUAKLUAUFMUCABCNOPUDUEKL $.
$}
