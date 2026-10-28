$( proofs/setmm/difference-laws/split-by-membership, elaborated from proofs/setmm/difference-laws.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/sets/subset-antisymmetric.mm $]

${
  $d k m $.
  $d A k m $.
  $d B k m $.
  proofs.setmm.difference-laws.split-by-membership $p |- ( ( A e. _V /\ B e. _V ) -> ( ( A i^i B ) u. ( A \ B ) ) = A ) $=
    ( cvv wcel wa cin cdif cun wss wceq simpl id syl inex1g difexg jca unexg vm cv wral simpr wb elin a1i mpbid simpld wn eldif wo elun mpjaodan ralrimiva dfss3 mpbird vk elun1 elun2 exmid stdlib.sets.subset-antisymmetric ) ACDZBCDZEZABFZABGZHZCDZUTEZVEAIZEZAVEIZEVEAJVBVIVJVBVGVHVBVFUTVBVCCDZVDCDZEVFVBVKVLVBUTVKVBUTUTUTVAKZUTLZMZABCNMVBUTVLVOABCOMPVCVDCCQMVOPVBVHRSZADZRVETZVBVQRVEVBVPVEDZEZVPVCDZVQVPVDDZVTWAEZVQVPBDZWCWAVQWDEZVTWAUAWAWEUBWCVPABUCUDUEUFVTWBEZVQWDUGZWFWBVQWGEZVTWBUAWBWHUBWFVPABUHUDUEUFVTVSWAWBUIZVBVSUAVSWIUBVTVPVCVDUJUDUEUKULVHVRUBVBRVEAUMUDUNPVBVJUOSZVEDZUOATZVBWKUOAVBWJADZEZWJBDZWKWOUGZWNWOEZWJVCDZWKWQWRWMWOEZWQWMWOWQWNWMWNWOKVBWMUAZMWNWOUAPWRWSUBWQWJABUCUDUNWJVCVDUPMWNWPEZWJVDDZWKXAXBWMWPEZXAWMWPXAWNWMWNWPKWTMWNWPUAPXBXCUBXAWJABUHUDUNWJVDVCUQMWOWPUIWNWOURUDUKULVJWLUBVBUOAVEUMUDUNPVEAUSM $.
$}
