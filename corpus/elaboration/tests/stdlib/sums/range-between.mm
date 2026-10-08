$( tests/stdlib/sums/range-between, elaborated from tests/stdlib/sums.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.sums.range-between $p |- ( ( ( ( ( A e. ZZ /\ B e. ZZ ) /\ C e. ZZ ) /\ B <_ A ) /\ A <_ C ) -> A e. ( B ... C ) ) $=
    ( cz wcel wa cle wbr cfz co simpl simpr syl jca w3a wb id 3jca elfz mpbird ) ADEZBDEZFZCDEZFZBAGHZFZACGHZFZABCIJZEZUFUHFZUIUFUHUIUGUFUGUHKZUEUFLMUGUHLNUIUAUBUDOUKULPUIUAUBUDUIUGUAUMUGUEUAUEUFKZUEUCUAUCUDKZUCUAUAUAUBKUAQMMMMUIUGUBUMUGUEUBUNUEUCUBUOUAUBLMMMUIUGUDUMUGUEUDUNUCUDLMMRABCSMT $.
$}
