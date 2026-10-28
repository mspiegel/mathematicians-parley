$( proofs/setmm/set-order-laws/union-equals-intersection, elaborated from proofs/setmm/set-order-laws.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/setmm/subset-of-union/subset-of-union.mm $]
$[ proofs/setmm/intersection-subsets/intersection-subset-right.mm $]
$[ proofs/setmm/subset-of-union-right/subset-of-union-right.mm $]
$[ proofs/setmm/intersection-subsets/intersection-subset-left.mm $]
$[ stdlib/sets/subset-antisymmetric.mm $]

${
  proofs.setmm.set-order-laws.union-equals-intersection $p |- ( ( A e. _V /\ B e. _V ) -> ( ( A u. B ) = ( A i^i B ) <-> A = B ) ) $=
    ( cvv wcel wa cun cin wceq wss simpl id syl simpr jca proofs.setmm.subset-of-union.subset-of-union sseq2d mpbid proofs.setmm.intersection-subsets.intersection-subset-right sstr proofs.setmm.subset-of-union-right.subset-of-union-right proofs.setmm.intersection-subsets.intersection-subset-left stdlib.sets.subset-antisymmetric eqcomd uneq2d unidm a1i eqtrd inidm ineq2d impbida ) ACDZBCDZEZABFZABGZHZABHZUMUPEZUMABIZEZBAIZEUQURUTVAURUMUSURUKULURUMUKUMUPJZUMUKUKUKULJZUKKZLZLZURUMULVBUKULMZLZNZURAUOIZUOBIZEUSURVJVKURAUNIZVJURUMVLVIABOLURUNUOAUMUPMZPQURUMVKVIABRLNAUOBSLNURBUOIZUOAIZEVAURVNVOURBUNIZVNURULUKEVPURULUKVHVFNBATLURUNUOBVMPQURUMVOVIABUALNBUOASLNABUBLUMUQEZUNAAGZUOVQUNAVRVQUNAAFZAVQBAAVQABUMUQMZUCZUDVSAHVQAUEUFUGVQVRAVRAHVQAUHUFUCUGVQUOVRVQBAAWAUIUCUGUJ $.
$}
