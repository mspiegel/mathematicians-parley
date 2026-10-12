$( tests/notations/groups/a-subgroup-test, elaborated from tests/notations/groups.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.notations.groups.a-subgroup-test $p |- ( ( ( ( A e. Grp /\ B e. ( SubGrp ` A ) ) /\ C e. B ) /\ D e. B ) -> ( C ( +g ` A ) ( ( invg ` A ) ` D ) ) e. B ) $=
    ( cgrp wcel csubg cfv wa cminusg w3a cplusg co simpl simpr syl jca eqid subginvcl 3jca subgcl ) AEFZBAGHZFZIZCBFZIZDBFZIZUDUFDAJHZHZBFZKCUKALHZMBFUIUDUFULUIUGUDUGUHNZUGUEUDUEUFNZUBUDOZPZPZUIUGUFUNUEUFOPUIUDUHIULUIUDUHURUGUHOQBAUJDUJRSPTUMBACUKUMRUAP $.
$}
