$( tests/elaborator/an-exhibit-from-an-and/one-witness-from-an-and, elaborated from tests/elaborator/an-exhibit-from-an-and.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A x $.
  $d B x $.
  $d C x $.
  tests.elaborator.an-exhibit-from-an-and.one-witness-from-an-and $p |- ( ( ( A e. _V /\ B e. A ) /\ C e. ( A \ { B } ) ) -> E. x e. A -. x = B ) $=
    ( cvv wcel wa csn cdif wceq wn cv wrex wne simpr eldifsn sylib wb df-ne a1i anbi2d mpbid simpl syl jca id eqeq1d notbid rspcev ) BEFZCBFZGZDBCHZIZFZGZDBFZDCJZKZGZALZCJZKZABMUPUQUSUPUTUQUPUQDCNZGZUTUPUOVEULUOOZDBCPZQZUPVDUSUQVDUSRZUPDCSZTZUAZUBZUQUSUCUDUPUTUSVMUQUSOUDUEVCUSADBVADJZVBURVNVADCVNUFUGUHUIUD $.
$}
