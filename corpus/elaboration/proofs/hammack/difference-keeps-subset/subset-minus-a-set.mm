$( proofs/hammack/difference-keeps-subset/subset-minus-a-set, elaborated from proofs/hammack/difference-keeps-subset.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A m $.
  $d B m $.
  $d C m $.
  proofs.hammack.difference-keeps-subset.subset-minus-a-set $p |- ( ( ( ( A e. _V /\ B e. _V ) /\ C e. _V ) /\ A C_ B ) -> ( A \ C ) C_ ( B \ C ) ) $=
    ( cvv wcel wa wss cdif vm cv wral wn simpl simpr syl wb eldif a1i mpbid jca ssel2 mpbird ralrimiva dfss3 ) ADEZBDEZFZCDEZFZABGZFZACHZBCHZGZIJZUMEZIULKZUKUPIULUKUOULEZFZUPUOBEZUOCEZLZFZUSUTVBUSUJUOAEZFUTUSUJVDUSUKUJUKURMUIUJNOUSVDVBFZVDUSURVEUKURNZURVEPZUSUOACQZRZSZVDVBMOTABUOUAOUSVEVBVJVDVBNOTUPVCPUSUOBCQRUBUCUNUQPUKIULUMUDRUB $.
$}
