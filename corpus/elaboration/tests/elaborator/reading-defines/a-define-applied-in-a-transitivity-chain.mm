$( tests/elaborator/reading-defines/a-define-applied-in-a-transitivity-chain, elaborated from tests/elaborator/reading-defines.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d k m $.
  $d A k m $.
  $d B k m $.
  $d C k m $.
  tests.elaborator.reading-defines.a-define-applied-in-a-transitivity-chain $p |- ( ( ( ( ( A e. NN /\ B e. RR ) /\ C e. RR ) /\ B < ( A + 1 ) ) /\ ( A + 1 ) < C ) -> B < C ) $=
    ( cn wcel cr wa c1 caddc co clt wbr vk cv vm cmpt wceq wex cvv nnex a1i mptexg syl elisset simpl simpr id nnre 1re readdcld cfv fveq1d eqid oveq1d ovex fvmptd3 eqtrd eqcomd breq2d mpbid breqtrd lttrd ex exlimdv mpd ) ADEZBFEZGZCFEZGZBAHIJZKLZGZVKCKLZGZMNZODONZHIJZPZQZMRZBCKLZVOVSSEZWAVODSEZWCWDVOTUAODVRSUBUCMVSSUDUCVOVTWBMVOVTWBVOVTGZBVKCWEVOVGVOVTUEZVOVMVGVMVNUEZVMVJVGVJVLUEZVJVHVGVHVIUEZVFVGUFUCUCUCUCWEAHWEVFAFEWEVOVFWFVOVMVFWGVMVJVFWHVJVHVFWIVHVFVFVFVGUEZVFUGZUCZUCZUCZUCZUCZAUHUCHFEWEUIUAUJWEVOVIWFVOVMVIWGVMVJVIWHVHVIUFUCUCUCWEBAVPUKZVKKWEVLBWQKLWEVOVLWFVOVMVLWGVJVLUFUCUCWEVKWQBKWEWQVKWEWQAVSUKZVKWEAVPVSVOVTUFZULZWEOAVRVKDVSSVSUMZVQAQZVQAHIXBUGZUNZWPVKSEZWEAHIUOZUAZUPZUQZURUSUTXIVAWEVOVNWFVMVNUFUCVBVCVDVE $.
$}
