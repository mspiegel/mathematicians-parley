$( proofs/wiedijk/wilson/below-not-divisible, elaborated from proofs/wiedijk/wilson.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  proofs.wiedijk.wilson.below-not-divisible $p |- ( ( ( A e. NN /\ B e. NN ) /\ B < A ) -> -. A || B ) $=
    ( cn wcel wa clt wbr cdvds wn simpl simpr syl cle cz wi id nnz jca dvdsle mpd cr wb nnre lenlt syl2anc mpbid pm2.21dd ex pm2.01d ) ACDZBCDZEZBAFGZEZABHGZUNUOUOIZUNUOEZUMUPUQUNUMUNUOJZULUMKLUQABMGZUMIZUQUOUSUNUOKUQANDZUKEUOUSOUQVAUKUQUJVAUQUNUJURUNULUJULUMJZULUJUJUJUKJZUJPZLZLZLZAQLUQUNUKURUNULUKVBUJUKKZLZLZRABSLTUQAUADZBUADZUSUTUBUQUJVKVGAUCLUQUKVLVJBUCLABUDUEUFUGUHUI $.
$}
