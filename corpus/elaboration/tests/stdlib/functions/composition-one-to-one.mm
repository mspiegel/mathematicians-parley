$( tests/stdlib/functions/composition-one-to-one, elaborated from tests/stdlib/functions.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.functions.composition-one-to-one $p |- ( ( ( ( ( A e. _V /\ B e. _V ) /\ C e. _V ) /\ ( D : A --> B /\ D : A -1-1-> B ) ) /\ ( E : B --> C /\ E : B -1-1-> C ) ) -> ( E o. D ) : A -1-1-> C ) $=
    ( cvv wcel wa wf wf1 ccom simpr syl simpl jca f1co ) AFGZBFGZHZCFGZHZABDIZABDJZHZHZBCEIZBCEJZHZHZUGUCHACEDKJUIUGUCUIUHUGUEUHLUFUGLMUIUDUCUIUEUDUEUHNUAUDLMUBUCLMOABCEDPM $.
$}
