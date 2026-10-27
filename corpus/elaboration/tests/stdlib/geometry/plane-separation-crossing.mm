$( tests/stdlib/geometry/plane-separation-crossing, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A m $.
  $d B m $.
  $d C m $.
  $d D m $.
  tests.stdlib.geometry.plane-separation-crossing $p |- ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. CC ) /\ -. A = B ) /\ ( ( Im ` ( ( C - A ) / ( B - A ) ) ) x. ( Im ` ( ( D - A ) / ( B - A ) ) ) ) < 0 ) -> E. m e. CC ( ( A = B \/ ( ( m - A ) / ( B - A ) ) e. RR ) /\ ( C =/= m /\ ( ( D - m ) / ( C - m ) ) e. RR /\ ( ( D - m ) / ( C - m ) ) < 0 ) ) ) $=
    ( cc wcel wa wceq wn cmin co cdiv cim cfv cmul cc0 clt wbr wne cv cr wo w3a wrex simpl id syl simpr jca neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid gplanesepcross ) AFGZBFGZHZCFGZHZDFGZHZABIZJZHZCAKLZBAKLZMLZNOZDAKLZVLMLZNOZPLZQRSZHZVGABTZHZVSHVHEUAZAKLVLMLUBGUCCWCTDWCKLZCWCKLZMLZUBGWFQRSUDHEFUEVTWBVSVTVGWAVTVEVFVTVCVDVTVAVBVTVJVAVJVSUFZVJVGVAVGVIUFZVGVEVAVEVFUFZVEVCVAVCVDUFZVCVAVAVAVBUFVAUGUHUHUHUHUHVTVJVBWGVJVGVBWHVGVEVBWIVEVCVBWJVAVBUIUHUHUHUHUJVTVJVDWGVJVGVDWHVGVEVDWIVCVDUIUHUHUHUJVTVJVFWGVJVGVFWHVEVFUIUHUHUJVTBAIZJZWAVTABVTVJVIWGVGVIUIUHUKVTWAWLVTWAVIWLWAVIULVTABUMUNVTVHWKVTWKVHWKVHULVTBAUOUNUPUQURUPUSUJVJVSUIUJEABCDUTUH $.
$}
