$( tests/stdlib/calculus/a-limit-below-a-late-bound, elaborated from tests/stdlib/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A n $.
  $d B n $.
  $d C n $.
  $d D n $.
  tests.stdlib.calculus.a-limit-below-a-late-bound $p |- ( ( ( ( ( ( A : NN --> RR /\ B e. RR ) /\ ( n e. NN |-> ( A ` n ) ) ~~> B ) /\ C e. RR ) /\ D e. NN ) /\ A. n e. NN ( D <_ n -> ( A ` n ) <_ C ) ) -> B <_ C ) $=
    ( cn cr wf wcel wa cv cfv cmpt cli wbr cle wi wral simpl id syl simpr glimle ) FGAHZBGIZJZEFEKZALZMZBNOZJZCGIZJZDFIZJZDUGPOZUHCPOZQZEFRZJZBCEADUTUOUDUOUSSZUOUMUDUMUNSZUMUKUDUKULSZUKUFUDUFUJSUFUDUDUDUESUDTUAUAUAUAUAUTUOUJVAUOUMUJVBUMUKUJVCUFUJUBUAUAUAUTUOULVAUOUMULVBUKULUBUAUAUTUOUNVAUMUNUBUAUOUSUBUC $.
$}
