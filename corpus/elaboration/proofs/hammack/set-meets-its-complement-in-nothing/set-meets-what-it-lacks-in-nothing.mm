$( proofs/hammack/set-meets-its-complement-in-nothing/set-meets-what-it-lacks-in-nothing, elaborated from proofs/hammack/set-meets-its-complement-in-nothing.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A m $.
  $d B m $.
  proofs.hammack.set-meets-its-complement-in-nothing.set-meets-what-it-lacks-in-nothing $p |- ( ( A e. _V /\ B e. _V ) -> ( A i^i ( B \ A ) ) = (/) ) $=
    ( cvv wcel wa vm cv wn cdif wral cin c0 wceq simpr wb eldif a1i mpbid syl ralrimiva disjr sylibr ) ACDZBCDZEZFGZADZHZFBAIZJAUIKLMUEUHFUIUEUFUIDZEZUFBDZUHEZUHUKUJUMUEUJNUJUMOUKUFBAPQRULUHNSTFAUIUAUB $.
$}
