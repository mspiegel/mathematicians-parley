$( tests/notations/sums/a-product-over-a-range-is-real, elaborated from tests/notations/sums.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A k $.
  $d B k $.
  tests.notations.sums.a-product-over-a-range-is-real $p |- ( ( A e. NN /\ B : ( 1 ... A ) --> RR ) -> prod_ k e. ( 1 ... A ) ( B ` k ) e. RR ) $=
    ( cn wcel c1 cfz co cr wf wa cv cfv cfn fzfi a1i simpl simpr syl ffvelcdm syl2anc fprodrecl ) ADEZFAGHZIBJZKZUDCLZBMZCUDNEUFFAOPUFUGUDEZKZUEUIUHIEUJUFUEUFUIQUCUERSUFUIRUDIUGBTUAUB $.
$}
