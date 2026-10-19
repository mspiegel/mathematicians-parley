$( tests/stdlib/numbers/cross-multiplied-order, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.cross-multiplied-order $p |- ( ( ( ( ( ( A e. RR /\ B e. RR ) /\ 0 < B ) /\ C e. RR ) /\ D e. RR ) /\ 0 < D ) -> ( ( A x. B ) < ( C x. D ) <-> ( A / D ) < ( C / B ) ) ) $=
    ( cr wcel wa cc0 clt wbr cmul co cdiv wb simpl id syl simpr jca lt2mul2div ) AEFZBEFZGZHBIJZGZCEFZGZDEFZGZHDIJZGZUAUBUDGZGZUFUHUJGZGZGABKLCDKLIJADMLCBMLIJNUKUMUOUKUAULUKUIUAUIUJOZUIUGUAUGUHOZUGUEUAUEUFOZUEUCUAUCUDOZUCUAUAUAUBOUAPQQQQQUKUBUDUKUIUBUPUIUGUBUQUGUEUBURUEUCUBUSUAUBRQQQQUKUIUDUPUIUGUDUQUGUEUDURUCUDRQQQSSUKUFUNUKUIUFUPUIUGUFUQUEUFRQQUKUHUJUKUIUHUPUGUHRQUIUJRSSSABCDTQ $.
$}
