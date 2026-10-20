$( tests/elaborator/a-value-at-a-point-said-once/an-item-at-a-value, elaborated from tests/elaborator/a-value-at-a-point-said-once.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.a-value-at-a-point-said-once.an-item-at-a-value $p |- ( ( A : NN --> RR /\ B e. NN ) -> ( abs ` ( A ` B ) ) e. RR ) $=
    ( cn cr wf wcel wa cfv cc cabs simpl id syl simpr ffvelcdm syl2anc recn abscl ) CDAEZBCFZGZBAHZIFZUBJHDFUAUBDFZUCUASTUDUASSSTKSLMSTNCDBAOPUBQMUBRM $.
$}
