$( tests/stdlib/calculus/continuous-is-bounded, elaborated from tests/stdlib/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d k m x y $.
  $d A k m x y $.
  $d B k m x y $.
  $d C k m x y $.
  tests.stdlib.calculus.continuous-is-bounded $p |- ( ( ( ( A e. RR /\ B e. RR ) /\ C : ( A [,] B ) --> RR ) /\ ( C |` ( A [,] B ) ) e. ( ( A [,] B ) -cn-> RR ) ) -> E. m e. RR A. y e. ( A [,] B ) ( abs ` ( C ` y ) ) <_ m ) $=
    ( cr wcel wa cicc co wf cres ccncf vx cv cfv cabs cle wbr wral wrex simpl id syl simpr gcncfbdd wb vk wceq fveq2d breq1d cbvralvw rexbii bitri a1i mpbid ) BFGZCFGZHZBCIJZFDKZHZDUTLZUTFMJZGZHZNOZDPZQPZEOZRSZNUTTZEFUAZAOZDPZQPZVJRSZAUTTZEFUAZVFENBCDVFVBUQVBVEUBZVBUSUQUSVAUBZUSUQUQUQURUBUQUCUDUDUDVFVBURVTVBUSURWAUQURUEUDUDVFVBVAVTUSVAUEUDVBVEUEUFVMVSUGVFVMUHOZDPZQPZVJRSZUHUTTZEFUAVSVLWFEFVKWENUHUTVGWBUIZVIWDVJRWGVHWCQWGVGWBDWGUCUJUJUKULUMWFVREFWEVQUHAUTWBVNUIZWDVPVJRWHWCVOQWHWBVNDWHUCUJUJUKULUMUNUOUP $.
$}
