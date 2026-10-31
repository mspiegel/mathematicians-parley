$( proofs/wiedijk/lagrange/coset-within, elaborated from proofs/wiedijk/lagrange.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d k m $.
  $d A k m $.
  $d B k m $.
  $d C k m $.
  proofs.wiedijk.lagrange.coset-within $p |- ( ( ( A e. Grp /\ B e. ( SubGrp ` A ) ) /\ C e. ( Base ` A ) ) -> ( { C } ( LSSum ` A ) B ) C_ ( Base ` A ) ) $=
    ( cgrp wcel csubg cfv wa cbs csn clsm co wss vm cv wral vk cplusg wceq wrex simpr w3a wb simpl id syl eqid subgss 3jca gelcoset mpbid jca ssel2 grpcl eqcomd eleq1d ex rexlimdva mpd ralrimiva dfss3 a1i mpbird ) ADEZBAFGZEZHZCAIGZEZHZCJZBAKGZLZVHMZNOZVHEZNVMPZVJVPNVMVJVOVMEZHZVOCQOZARGZLZSZQBTZVPVSVRWDVJVRUAVSVDBVHMZVIUBVRWDUCVSVDWEVIVSVJVDVJVRUDZVJVGVDVGVIUDZVGVDVDVDVFUDZVDUEZUFZUFZUFZVSVFWEVSVJVFWFVJVGVFWGVDVFUAZUFZUFVHBAVHUGZUHZUFVSVJVIWFVGVIUAZUFZUIQCBAVOUJUFUKVSWCVPQBVSVTBEZHZWCVPWTWCHZWBVHEZVPXAVDVIVTVHEZUBXBXAVDVIXCXAWTVDWTWCUDZWTVSVDVSWSUDZWLUFUFXAWTVIXDWTVSVIXEWRUFUFXAWEWSHXCXAWEWSXAWTWEXDWTVSWEXEVSVJWEWFVJVFWEWNWPUFUFUFUFXAWTWSXDVSWSUAUFULBVHVTUMUFUIVHWAACVTWOWAUGUNUFXAWBVOVHXAVOWBWTWCUAUOUPUKUQURUSUTVNVQUCVJNVMVHVAVBVC $.
$}
