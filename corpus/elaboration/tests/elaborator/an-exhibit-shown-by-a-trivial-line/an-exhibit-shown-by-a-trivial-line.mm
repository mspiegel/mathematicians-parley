$( tests/elaborator/an-exhibit-shown-by-a-trivial-line/an-exhibit-shown-by-a-trivial-line, elaborated from tests/elaborator/an-exhibit-shown-by-a-trivial-line.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A n $.
  $d B n $.
  tests.elaborator.an-exhibit-shown-by-a-trivial-line.an-exhibit-shown-by-a-trivial-line $p |- ( ( A e. NN /\ B e. NN ) -> E. n e. NN ( A x. B ) = ( A x. n ) ) $=
    ( cn wcel wa cmul co wceq cv wrex simpr c1 cexp cc simpl id syl nncn exp1 eqcomd cn0 1nn0 a1i expcld mullid eqtrd oveq12d ax-1cn jca mul4 mulridi eqidd eqtr4d oveq2d eqeq2d rspcev ) ADEZBDEZFZUSABGHZVAIZFVAACJZGHZIZCDKUTUSVBURUSLZUTVAVAUTVAVAUTVAMAMNHZBMNHZGHZGHZVAUTVAMVGGHZMVHGHZGHZVJUTAVKBVLGUTAVGVKUTVGAUTAOEZVGAIZUTURVNUTURURURUSPZURQZRZASZRZATZRZUAZUTVKVGUTVGOEZVKVGIZUTAMVTMUBEZUTUCUDZUEZVGUFZRZUAZUGZUTBVHVLUTVHBUTBOEZVHBIZUTUSWMVFBSZRZBTZRZUAZUTVLVHUTVHOEZVLVHIZUTBMWPWGUEZVHUFZRZUAZUGZUHZUTVMMMGHZVIGHZVJUTMOEZWDFZXJWTFZFZVMXIIZUTXKXLUTXJWDXJUTUIUDZWHUJZUTXJWTXOXBUJZUJZMVGMVHUKZRZUTXHMVIVIGXHMIZUTMUIULZUDZUTVIUMZUHZUGZUGZYGUNUAUAUJVEVBCBDVCBIZVDVAVAYHVCBAGYHQUOUPUQR $.
$}
