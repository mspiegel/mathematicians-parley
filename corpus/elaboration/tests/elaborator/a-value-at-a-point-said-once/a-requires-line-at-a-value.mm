$( tests/elaborator/a-value-at-a-point-said-once/a-requires-line-at-a-value, elaborated from tests/elaborator/a-value-at-a-point-said-once.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.a-value-at-a-point-said-once.a-requires-line-at-a-value $p |- ( ( ( A : NN --> RR /\ B e. NN ) /\ C e. RR ) -> ( abs ` ( ( A ` B ) - C ) ) e. RR ) $=
    ( cn cr wf wcel wa cfv cmin co cc cabs simpl id syl simpr ffvelcdm syl2anc resubcld recn abscl ) DEAFZBDGZHZCEGZHZBAIZCJKZLGZUIMIEGUGUIEGUJUGUHCUGUCUDUHEGUGUEUCUEUFNZUEUCUCUCUDNUCOPPUGUEUDUKUCUDQPDEBARSUEUFQTUIUAPUIUBP $.
$}
