$( proofs/setmm/inverse-lands-in-domain/inverse-lands-in-domain, elaborated from proofs/setmm/inverse-lands-in-domain.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]
$[ proofs/setmm/value-of-onto/value-of-onto.mm $]

${
  $d k m x $.
  $d A k m x $.
  $d B k m x $.
  $d C k m x $.
  $d D k m x $.
  proofs.setmm.inverse-lands-in-domain.inverse-lands-in-domain $p |- ( ( ( ( ( A e. _V /\ B e. _V ) /\ ( C : A --> B /\ C : A -1-1-> B ) ) /\ ( C " A ) = B ) /\ D e. B ) -> ( `' C ` D ) e. A ) $=
    ( cvv wcel wa wf wf1 cima wceq vm cv cfv wrex ccnv vx simpl id syl simpr jca proofs.setmm.value-of-onto.value-of-onto wb vk fveq2d eqeq2d cbvrexvw bitri a1i mpbid gf1cnvfv1 eqcomd eqeq1d eleq1d ex rexlimdva mpd ) AEFZBEFZGZABCHZABCIZGZGZCAJZBKZGZDBFZGZDLMZCNZKZLAOZDCPZNZAFZVJDQMZCNZKZQAOZVNVJVAVBGZVGGZVIGWAVJWCVIVJWBVGVJVAVBVJUSUTVJVHUSVHVIRZVHVEUSVEVGRZVEVAUSVAVDRZVAUSUSUSUTRUSSTTTTVJVHUTWDVHVEUTWEVEVAUTWFUSUTUATTTUBVJVDVBVJVHVDWDVHVEVDWEVAVDUAZTZTZVBVCRTUBVJVHVGWDVEVGUATUBVHVIUAUBQABCDUCTWAVNUDVJWADUEMZCNZKZUEAOVNVTWLQUEAVRWJKZVSWKDWMVRWJCWMSUFUGUHWLVMUELAWJVKKZWKVLDWNWJVKCWNSUFUGUHUIUJUKVJVMVQLAVJVKAFZGZVMVQWPVMGZWOVQWQWPWOWPVMRZVJWOUAZTZWQVKVPAWQVPVKWQVLVONZVKKZVPVKKWQVCWOGXBWQVCWOWQVDVCWQWPVDWRWPVJVDVJWORWITTVBVCUATWTUBABVKCULTWQXAVPVKWQVLDVOWQDVLWPVMUAUMUFUNUKUMUOUKUPUQUR $.
$}
