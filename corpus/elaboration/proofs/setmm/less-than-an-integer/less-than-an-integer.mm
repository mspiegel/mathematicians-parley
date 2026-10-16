$( proofs/setmm/less-than-an-integer/less-than-an-integer, elaborated from proofs/setmm/less-than-an-integer.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  proofs.setmm.less-than-an-integer.less-than-an-integer $p |- ( ( A e. RR /\ B e. ZZ ) -> ( A < B <-> ( |_ ` A ) < B ) ) $=
    ( cr wcel cz wa clt wbr cfl cfv simpl id syl flcl zre simpr cle flle lelttrd c1 caddc co 1re a1i readdcld flltp1 wb jca zltp1le mpbid ltletrd impbida ) ACDZBEDZFZABGHZAIJZBGHZUOUPFZUQABUSUQEDZUQCDZUSUOUTUOUPKZUOUMUTUOUMUMUMUNKZUMLZMZANZMZMUQOZMUSUOUMVBVEMUSUNBCDZUSUOUNVBUMUNPZMBOZMUSUOUQAQHZVBUOUMVLVEARMMUOUPPSUOURFZAUQTUAUBZBVMUOUMUOURKZVEMVMUQTVMUTVAVMUOUTVOVGMZVHMTCDVMUCUDUEVMUNVIVMUOUNVOVJMZVKMVMUOAVNGHZVOUOUMVRVEAUFMMVMURVNBQHZUOURPVMUTUNFURVSUGVMUTUNVPVQUHUQBUIMUJUKUL $.
$}
