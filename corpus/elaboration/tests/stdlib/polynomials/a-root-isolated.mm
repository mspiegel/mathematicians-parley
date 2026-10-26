$( tests/stdlib/polynomials/a-root-isolated, elaborated from tests/stdlib/polynomials.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d m r $.
  $d A m r $.
  $d B m r $.
  $d C m r $.
  tests.stdlib.polynomials.a-root-isolated $p |- ( ( ( ( ( ( A : CC --> CC /\ A e. ( Poly ` ZZ ) ) /\ B e. NN ) /\ ( deg ` A ) = B ) /\ C e. RR ) /\ ( A ` C ) = 0 ) -> E. m e. RR ( 0 < m /\ A. r e. RR ( ( ( abs ` ( C - r ) ) <_ m /\ ( A ` r ) = 0 ) -> r = C ) ) ) $=
    ( cc wf cz cply cfv wcel wa cn cdgr wceq cr cc0 simpl simpr syl grootsiso ) FFAGZAHIJZKZLZBMKZLZANJZBOZLZCPKZLZCAJZQOZLZCABEDUOULUDULUNRZULUJUDUJUKRZUJUGUDUGUIRZUGUEUDUEUFRUBUDSTTTTUOULUFUPULUJUFUQUJUGUFURUEUFSTTTUOULUIUPULUJUIUQUGUISTTUOULUKUPUJUKSTUA $.
$}
