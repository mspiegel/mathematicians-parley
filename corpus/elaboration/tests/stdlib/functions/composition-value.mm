$( tests/stdlib/functions/composition-value, elaborated from tests/stdlib/functions.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.functions.composition-value $p |- ( ( ( ( ( ( A e. _V /\ B e. _V ) /\ C e. _V ) /\ D : A --> B ) /\ E : B --> C ) /\ F e. A ) -> ( ( E o. D ) ` F ) = ( E ` ( D ` F ) ) ) $=
    ( cvv wcel wa wf ccom cfv wceq simpl simpr syl jca fvco3 ) AGHZBGHZIZCGHZIZABDJZIZBCEJZIZFAHZIZUDUHIFEDKLFDLELMUIUDUHUIUGUDUGUHNUGUEUDUEUFNUCUDOPPUGUHOQABFEDRP $.
$}
