$( tests/elaborator/chains/a-pair-on-a-calculation-line, elaborated from tests/elaborator/chains.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.chains.a-pair-on-a-calculation-line $p |- ( ( ( ( ( ( A e. RR /\ B e. RR ) /\ C e. RR ) /\ D e. RR ) /\ ( B = C /\ C = D ) ) /\ A = B ) -> A = D ) $=
    ( cr wcel wa wceq simpr simpl syl simpld simprd eqtrd ) AEFZBEFZGZCEFZGZDEFZGZBCHZCDHZGZGZABHZGZABDUEUFIUGBCDUGUBUCUGUEUDUEUFJZUAUDIZKZLUGUBUCUJMNN $.
$}
