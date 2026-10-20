$( proofs/hammack/disjoint-power-set-difference/disjoint-power-set-difference, elaborated from proofs/hammack/disjoint-power-set-difference.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d k m $.
  $d A k m $.
  $d B k m $.
  proofs.hammack.disjoint-power-set-difference.disjoint-power-set-difference $p |- ( ( ( A e. _V /\ B e. _V ) /\ ( A i^i B ) = (/) ) -> ( ~P A \ ~P B ) C_ ~P ( A \ B ) ) $=
    ( cvv wcel wa cin c0 wceq cpw cdif wss vm cv wral vk wn simpl simpr wb eldif a1i mpbid syl vex elpwg jca ssel2 disjel mpbird ralrimiva dfss3 ) ACDZBCDZEZABFZGHZEZAIZBIZJZABJZIZKZLMZVBDZLUTNZUQVELUTUQVDUTDZEZVEVDVAKZVHVIOMZVADZOVDNZVHVKOVDVHVJVDDZEZVKVJADZVJBDZPZEZVNVOVQVNVDAKZVMEZVOVNVSVMVNVHVSVHVMQZVHVDURDZVSVHWBVDUSDZPZEZWBVHVGWEUQVGRZVGWESZVHVDURUSTZUAZUBZWBWDQZUCZVHVDCDZWBVSSZWMVHLUDZUAZVDACUEZUCZUBZUCZVHVMRZUFZVDAVJUGZUCZVNUPVOEVQVNUPVOVNVHUPWAVHUQUPUQVGQUNUPRUCUCXDUFABVJUHUCUFVKVRSVNVJABTUAUIUJVIVLSVHOVDVAUKUAUIVHWMVEVISWPVDVACUEUCUIUJVCVFSUQLUTVBUKUAUI $.
$}
