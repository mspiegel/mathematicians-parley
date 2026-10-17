$( proofs/setmm/group-cancellation/quotient-times-divisor, elaborated from proofs/setmm/group-cancellation.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/setmm/group-cancellation/the-left-inverse.mm $]

${
  proofs.setmm.group-cancellation.quotient-times-divisor $p |- ( ( ( A e. Grp /\ B e. ( Base ` A ) ) /\ C e. ( Base ` A ) ) -> ( ( B ( +g ` A ) ( ( invg ` A ) ` C ) ) ( +g ` A ) C ) = B ) $=
    ( cgrp wcel cbs cfv wa cminusg cplusg co c0g wceq w3a simpl id syl simpr jca eqid grpinvcl 3jca grpass proofs.setmm.group-cancellation.the-left-inverse oveq2d eqeq2d mpbid grprid eqtrd ) ADEZBAFGZEZHZCUKEZHZBCAIGZGZAJGZKZCURKZBALGZURKZBUOUTBUQCURKZURKZMZUTVBMUOUJULUQUKEZUNNZHVEUOUJVGUOUMUJUMUNOZUMUJUJUJULOZUJPZQZQZUOULVFUNUOUMULVHUJULRZQZUOUJUNHZVFUOUJUNVLUMUNRZSZUKAUPCUKTZUPTUAQVPUBSUKURABUQCVRURTZUCQUOVDVBUTUOVCVABURUOVOVCVAMVQACUDQUEUFUGUOUMVBBMUOUJULVLVNSUKURABVAVRVSVATUHQUI $.
$}
