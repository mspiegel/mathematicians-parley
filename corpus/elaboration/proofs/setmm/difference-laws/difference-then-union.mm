$( proofs/setmm/difference-laws/difference-then-union, elaborated from proofs/setmm/difference-laws.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  proofs.setmm.difference-laws.difference-then-union $p |- ( ( A e. _V /\ B e. _V ) -> ( ( A \ B ) u. B ) = ( A u. B ) ) $=
    ( cvv wcel wa cdif cun wceq uncom a1i undif2 eqtrd ) ACDZBCDZEZABFZBGZBAGZABGZOQBPGZRQTHOPBIJTRHOBAKJLRSHOBAIJL $.
$}
