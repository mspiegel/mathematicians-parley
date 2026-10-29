$( proofs/setmm/set-order-laws/subset-iff-difference-empty, elaborated from proofs/setmm/set-order-laws.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/setmm/subset-of-union-right/subset-of-union-right.mm $]

${
  proofs.setmm.set-order-laws.subset-iff-difference-empty $p |- ( ( A e. _V /\ B e. _V ) -> ( A C_ B <-> ( A \ B ) = (/) ) ) $=
    ( cvv wcel wa wss cdif c0 wceq simpr ssdif syl difid a1i sseq2d mpbid ss0b sylib cun simpl id jca proofs.setmm.subset-of-union-right.subset-of-union-right un0 wb eqcom undif2 uneq2d eqeq1d eqtrd eqcomd impbida ) ACDZBCDZEZABFZABGZHIZUOUPEZUQHFZURUSUQBBGZFZUTUSUPVBUOUPJABBKLUSVAHUQVAHIUSBMNOPUQQRUOUREZABASZFZUPVCUOVEVCUMUNVCUOUMUOURTZUOUMUMUMUNTUMUALLVCUOUNVFUMUNJLUBABUCLVCVDBAVCBVDVCBBHSZVDVCVGBIZBVGIZVHVCBUDNVHVIUEVCVGBUFNPVCBUQSZVDIZVGVDIVKVCBAUGNVCVJVGVDVCUQHBUOURJUHUIPUJUKOPUL $.
$}
