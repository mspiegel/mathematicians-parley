$( tests/elaborator/mod-on-the-reals/one-mod-a-real, elaborated from tests/elaborator/mod-on-the-reals.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.elaborator.mod-on-the-reals.one-mod-a-real $p |- ( ( A e. RR /\ 1 < A ) -> ( 1 mod A ) = 1 ) $=
    ( cr wcel c1 clt wbr wa cc0 cle cmo co wceq 1re a1i simpl id syl jca 0lt1 wi 0re ltle syl2anc mpd simpr gmodid ) ABCZDAEFZGZDBCZUGGZHDIFZUHGZGDAJKDLUIUKUMUIUJUGUJUIMNZUIUGUGUGUHOUGPQRUIULUHUIHDEFZULUOUISNUIHBCZUJUOULTUPUIUANUNHDUBUCUDUGUHUERRDAUFQ $.
$}
