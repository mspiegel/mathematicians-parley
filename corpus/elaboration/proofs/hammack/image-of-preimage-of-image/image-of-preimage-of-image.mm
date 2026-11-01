$( proofs/hammack/image-of-preimage-of-image/image-of-preimage-of-image, elaborated from proofs/hammack/image-of-preimage-of-image.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]
$[ proofs/hammack/preimage-of-image/subset-of-preimage-of-image.mm $]
$[ stdlib/sets/subset-antisymmetric.mm $]

${
  $d j k m $.
  $d A j k m $.
  $d B j k m $.
  $d C j k m $.
  $d D j k m $.
  proofs.hammack.image-of-preimage-of-image.image-of-preimage-of-image $p |- ( ( ( ( A e. _V /\ B e. _V ) /\ C : A --> B ) /\ D e. ~P A ) -> ( C " ( `' C " ( C " D ) ) ) = ( C " D ) ) $=
    ( cvv wcel wa wf cpw ccnv cima wss wceq simpl simpr syl id jca fex imaexg vk cv wral vj cfv wrex wb vm gelpreima mpbid ralrimiva dfss3 a1i mpbird gfvelima eqcomd eleq1d ex rexlimdva mpd proofs.hammack.preimage-of-image.subset-of-preimage-of-image imass2 stdlib.sets.subset-antisymmetric ) AEFZBEFZGZABCHZGZDAIZFZGZCCJZCDKZKZKZEFZVMEFZGZVOVMLZGZVMVOLZGVOVMMVKVTWAVKVRVSVKVPVQVKCEFZVPVKVGVDGZWBVKVGVDVKVHVGVHVJNZVFVGOZPZVKVHVDWDVHVFVDVFVGNZVFVDVDVDVENZVDQZPZPZPZRZABECSZPZCVNETPVKWBVQWOCDETPRVKVSUAUBZVMFZUAVOUCZVKWQUAVOVKWPVOFZGZWPUDUBZCUEZMZUDVNUFZWQWTWSXDVKWSOWTVGVNALZGWSXDUGWTVGXEWTVKVGVKWSNZWFPZWTVKXEXFVKXEUHUBZAFZUHVNUCZVKXIUHVNVKXHVNFZGZXIXHCUEZVMFZGZXIXLXKXOVKXKOXLVGXKXOUGXLVKVGVKXKNWFPABXHVMCUIPUJXIXNNPUKXEXJUGVKUHVNAULUMUNPRUDABWPVNCUOPUJWTXCWQUDVNWTXAVNFZGZXCWQXQXCGZXBVMFZWQXRXAAFZXSGZXSXRXPYAXRXQXPXQXCNZWTXPOPXRVGXPYAUGXRXQVGYBXQWTVGWTXPNXGPPABXAVMCUIPUJXTXSOPXRXBWPVMXRWPXBXQXCOUPUQUJURUSUTUKVSWRUGVKUAVOVMULUMUNRVKDVNLZWAVKVKYCVKVHVJVKVFVGVKVDVEWLVKVHVEWDVHVFVEWGVDVEOPPRWFRVHVJORABCDVAPDVNCVBPRVOVMVCP $.
$}
