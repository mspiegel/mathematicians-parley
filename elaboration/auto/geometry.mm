$( geometry, built by elaboration/build-geometry.py.

   What this corpus needs of the plane and set.mm does not state.
   Points are complex numbers, distance is the absolute value of a
   difference, and the angle is the constant definitions.mm introduces,
   so everything here is a theorem rather than an axiom: CC is a model
   and nothing in it has to be assumed.  GEOMETRY.md takes that
   decision and says what it costs. $)

$[ definitions.mm $]

$( `angval` reads a value of the angle by substituting for the two names
   `df-ang` binds, and asks that they be free of what is substituted. They
   appear in no statement here, only inside the proofs. The pairs are
   written one at a time because `$d x y A B` would also hold A and B
   apart, and the lemmas below are applied at terms that share names. $)
$d x y $.
$d x A $.  $d y A $.
$d x B $.  $d y B $.
$d x C $.  $d y C $.
$d x P $.  $d y P $.
$d x Q $.  $d y Q $.
$d x R $.  $d y R $.
$d x S $.  $d y S $.
$d x T $.  $d y T $.
$d x U $.  $d y U $.

  gtrirec $p |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) -> ( ( A / B ) e. RR -> ( B / A ) e. RR ) ) $=
    cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cB cdiv co cr
    wcel cB cA cdiv co cr wcel cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne
    wa wa cA cB cdiv co cr wcel wa c1 cA cB cdiv co cdiv co cB cA cdiv co cr
    cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa c1 cA cB cdiv co
    cdiv co cB cA cdiv co wceq cA cB cdiv co cr wcel cA cB recdiv adantr cA
    cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cB cdiv co cr wcel
    wa cA cB cdiv co cr wcel cA cB cdiv co cc0 wne wa c1 cA cB cdiv co cdiv
    co cr wcel cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cB
    cdiv co cr wcel wa cA cB cdiv co cr wcel cA cB cdiv co cc0 wne cA cc wcel
    cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cB cdiv co cr wcel simpr cA
    cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cB cdiv co cc0 wne
    cA cB cdiv co cr wcel cA cB divne0 adantr jca cA cB cdiv co rereccl syl
    eqeltrrd ex $.

  gtriswap $p |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( ( ( -. A = B /\ -. B = C ) /\ -. A = C ) /\ -. ( ( C - A ) / ( B - A ) ) e. RR ) -> ( ( ( -. A = C /\ -. C = B ) /\ -. A = B ) /\ -. ( ( B - A ) / ( C - A ) ) e. RR ) ) ) $=
    cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC
    wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa cA cC wceq
    wn cC cB wceq wn wa cA cB wceq wn wa cB cA cmin co cC cA cmin co cdiv co
    cr wcel wn wa cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC
    wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel
    wn wa wa cA cC wceq wn cC cB wceq wn wa cA cB wceq wn wa cB cA cmin co cC
    cA cmin co cdiv co cr wcel wn cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co
    cdiv co cr wcel wn wa wa cA cC wceq wn cC cB wceq wn cA cB wceq wn cA cc
    wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq
    wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa cA cB wceq wn
    cB cC wceq wn wa cA cC wceq wn cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co
    cdiv co cr wcel wn wa wa cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa
    cC cA cmin co cB cA cmin co cdiv co cr wcel wn cA cc wcel cB cc wcel cC
    cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co
    cB cA cmin co cdiv co cr wcel wn wa simpr simpld simprd cA cc wcel cB cc
    wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA
    cmin co cB cA cmin co cdiv co cr wcel wn wa wa cC cB cA cc wcel cB cc
    wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA
    cmin co cB cA cmin co cdiv co cr wcel wn wa wa cB cC cA cc wcel cB cc
    wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA
    cmin co cB cA cmin co cdiv co cr wcel wn wa wa cB cC cA cc wcel cB cc
    wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA
    cmin co cB cA cmin co cdiv co cr wcel wn wa wa cA cB wceq wn cB cC wceq
    wn cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA
    cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa cA cB
    wceq wn cB cC wceq wn wa cA cC wceq wn cA cc wcel cB cc wcel cC cc wcel
    w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA
    cmin co cdiv co cr wcel wn wa wa cA cB wceq wn cB cC wceq wn wa cA cC
    wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn cA cc wcel cB
    cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC
    cA cmin co cB cA cmin co cdiv co cr wcel wn wa simpr simpld simpld simprd
    neqned necomd neneqd cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn
    cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr
    wcel wn wa wa cA cB wceq wn cB cC wceq wn cA cc wcel cB cc wcel cC cc
    wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB
    cA cmin co cdiv co cr wcel wn wa wa cA cB wceq wn cB cC wceq wn wa cA cC
    wceq wn cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn
    wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa
    cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin
    co cdiv co cr wcel wn cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn
    cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr
    wcel wn wa simpr simpld simpld simpld jca31 cA cc wcel cB cc wcel cC cc
    wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB
    cA cmin co cdiv co cr wcel wn wa wa cC cA cmin co cB cA cmin co cdiv co
    cr wcel wn cB cA cmin co cC cA cmin co cdiv co cr wcel wn cA cc wcel cB
    cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC
    cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa cA cB wceq wn cB cC
    wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel
    wn cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA
    cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa simpr
    simprd cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn
    wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa
    cB cA cmin co cC cA cmin co cdiv co cr wcel cC cA cmin co cB cA cmin co
    cdiv co cr wcel cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC
    wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel
    wn wa wa cB cA cmin co cc wcel cB cA cmin co cc0 wne wa cC cA cmin co cc
    wcel cC cA cmin co cc0 wne wa wa cB cA cmin co cC cA cmin co cdiv co cr
    wcel cC cA cmin co cB cA cmin co cdiv co cr wcel wi cA cc wcel cB cc wcel
    cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin
    co cB cA cmin co cdiv co cr wcel wn wa wa cB cA cmin co cc wcel cB cA
    cmin co cc0 wne wa cC cA cmin co cc wcel cC cA cmin co cc0 wne wa cA cc
    wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq
    wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa cB cA cmin co
    cc wcel cB cA cmin co cc0 wne cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co
    cdiv co cr wcel wn wa wa cB cA cA cc wcel cB cc wcel cC cc wcel w3a cB cc
    wcel cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA
    cmin co cdiv co cr wcel wn wa cA cc wcel cB cc wcel cC cc wcel simp2
    adantr cA cc wcel cB cc wcel cC cc wcel w3a cA cc wcel cA cB wceq wn cB
    cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr
    wcel wn wa cA cc wcel cB cc wcel cC cc wcel simp1 adantr subcld cA cc
    wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq
    wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa cB cA cmin co
    cc0 wne cB cA wne cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB
    cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr
    wcel wn wa wa cB cA cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB
    cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr
    wcel wn wa wa cB cA cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB
    cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr
    wcel wn wa wa cA cB cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB
    cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr
    wcel wn wa wa cA cB cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB
    cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr
    wcel wn wa wa cA cB wceq wn cB cC wceq wn cA cc wcel cB cc wcel cC cc
    wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB
    cA cmin co cdiv co cr wcel wn wa wa cA cB wceq wn cB cC wceq wn wa cA cC
    wceq wn cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn
    wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa
    cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin
    co cdiv co cr wcel wn cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn
    cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr
    wcel wn wa simpr simpld simpld simpld neqned necomd neneqd neqned cA cc
    wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq
    wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa cB cA cmin co
    cc0 cB cA cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq
    wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa
    wa cB cA cA cc wcel cB cc wcel cC cc wcel w3a cB cc wcel cA cB wceq wn cB
    cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr
    wcel wn wa cA cc wcel cB cc wcel cC cc wcel simp2 adantr cA cc wcel cB cc
    wcel cC cc wcel w3a cA cc wcel cA cB wceq wn cB cC wceq wn wa cA cC wceq
    wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa cA cc wcel cB cc
    wcel cC cc wcel simp1 adantr subeq0ad necon3bid mpbird jca cA cc wcel cB
    cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC
    cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa cC cA cmin co cc wcel
    cC cA cmin co cc0 wne cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn
    cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr
    wcel wn wa wa cC cA cA cc wcel cB cc wcel cC cc wcel w3a cC cc wcel cA cB
    wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co
    cdiv co cr wcel wn wa cA cc wcel cB cc wcel cC cc wcel simp3 adantr cA cc
    wcel cB cc wcel cC cc wcel w3a cA cc wcel cA cB wceq wn cB cC wceq wn wa
    cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa cA cc
    wcel cB cc wcel cC cc wcel simp1 adantr subcld cA cc wcel cB cc wcel cC
    cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co
    cB cA cmin co cdiv co cr wcel wn wa wa cC cA cmin co cc0 wne cC cA wne cA
    cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC
    wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa cC cA cA
    cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC
    wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa cC cA cA
    cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC
    wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa cA cC cA
    cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC
    wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa cA cC cA
    cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC
    wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa cA cB
    wceq wn cB cC wceq wn wa cA cC wceq wn cA cc wcel cB cc wcel cC cc wcel
    w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA
    cmin co cdiv co cr wcel wn wa wa cA cB wceq wn cB cC wceq wn wa cA cC
    wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn cA cc wcel cB
    cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC
    cA cmin co cB cA cmin co cdiv co cr wcel wn wa simpr simpld simprd neqned
    necomd neneqd neqned cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn
    cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr
    wcel wn wa wa cC cA cmin co cc0 cC cA cA cc wcel cB cc wcel cC cc wcel
    w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA
    cmin co cdiv co cr wcel wn wa wa cC cA cA cc wcel cB cc wcel cC cc wcel
    w3a cC cc wcel cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin
    co cB cA cmin co cdiv co cr wcel wn wa cA cc wcel cB cc wcel cC cc wcel
    simp3 adantr cA cc wcel cB cc wcel cC cc wcel w3a cA cc wcel cA cB wceq
    wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co
    cr wcel wn wa cA cc wcel cB cc wcel cC cc wcel simp1 adantr subeq0ad
    necon3bid mpbird jca jca cB cA cmin co cC cA cmin co gtrirec syl con3d
    mpd jca ex $.

  gtricol $p |- ( ( ( A e. CC /\ B e. CC /\ C e. CC ) /\ ( ( A - B ) =/= 0 /\ ( C - B ) =/= 0 ) ) -> ( ( ( A - B ) / ( C - B ) ) e. RR -> ( ( C - A ) / ( B - A ) ) e. RR ) ) $=
    cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB cmin co
    cc0 wne wa wa cA cB cmin co cC cB cmin co cdiv co cr wcel cC cA cmin co
    cB cA cmin co cdiv co cr wcel cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA cB cmin co cC cB cmin co
    cdiv co cr wcel wa cC cA cmin co cB cA cmin co cdiv co c1 cC cB cmin co
    cA cB cmin co cdiv co cmin co cr cA cc wcel cB cc wcel cC cc wcel w3a cA
    cB cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA cB cmin co cC cB cmin
    co cdiv co cr wcel wa cA cC cmin co cneg cA cB cmin co cneg cdiv co cA cC
    cmin co cA cB cmin co cdiv co cC cA cmin co cB cA cmin co cdiv co c1 cC
    cB cmin co cA cB cmin co cdiv co cmin co cA cc wcel cB cc wcel cC cc wcel
    w3a cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA cB cmin co cC cB
    cmin co cdiv co cr wcel wa cA cC cmin co cc wcel cA cB cmin co cc wcel cA
    cB cmin co cc0 wne cA cC cmin co cneg cA cB cmin co cneg cdiv co cA cC
    cmin co cA cB cmin co cdiv co wceq cA cc wcel cB cc wcel cC cc wcel w3a
    cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA cB cmin co cC cB
    cmin co cdiv co cr wcel wa cA cC cA cc wcel cB cc wcel cC cc wcel w3a cA
    cB cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA cc wcel cA cB cmin co
    cC cB cmin co cdiv co cr wcel cA cc wcel cB cc wcel cC cc wcel w3a cA cc
    wcel cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa cA cc wcel cB cc wcel
    cC cc wcel simp1 adantr adantr cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    cmin co cc0 wne cC cB cmin co cc0 wne wa wa cC cc wcel cA cB cmin co cC
    cB cmin co cdiv co cr wcel cA cc wcel cB cc wcel cC cc wcel w3a cC cc
    wcel cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa cA cc wcel cB cc wcel
    cC cc wcel simp3 adantr adantr subcld cA cc wcel cB cc wcel cC cc wcel
    w3a cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA cB cmin co cC cB
    cmin co cdiv co cr wcel wa cA cB cA cc wcel cB cc wcel cC cc wcel w3a cA
    cB cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA cc wcel cA cB cmin co
    cC cB cmin co cdiv co cr wcel cA cc wcel cB cc wcel cC cc wcel w3a cA cc
    wcel cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa cA cc wcel cB cc wcel
    cC cc wcel simp1 adantr adantr cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    cmin co cc0 wne cC cB cmin co cc0 wne wa wa cB cc wcel cA cB cmin co cC
    cB cmin co cdiv co cr wcel cA cc wcel cB cc wcel cC cc wcel w3a cB cc
    wcel cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa cA cc wcel cB cc wcel
    cC cc wcel simp2 adantr adantr subcld cA cc wcel cB cc wcel cC cc wcel
    w3a cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA cB cmin co cc0
    wne cA cB cmin co cC cB cmin co cdiv co cr wcel cA cB cmin co cc0 wne cC
    cB cmin co cc0 wne wa cA cB cmin co cc0 wne cA cc wcel cB cc wcel cC cc
    wcel w3a cA cB cmin co cc0 wne cC cB cmin co cc0 wne simpl adantl adantr
    cA cC cmin co cA cB cmin co div2neg syl3anc cA cc wcel cB cc wcel cC cc
    wcel w3a cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA cB cmin co
    cC cB cmin co cdiv co cr wcel wa cA cC cmin co cneg cC cA cmin co cA cB
    cmin co cneg cB cA cmin co cdiv cA cc wcel cB cc wcel cC cc wcel w3a cA
    cB cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA cB cmin co cC cB cmin
    co cdiv co cr wcel wa cA cc wcel cC cc wcel cA cC cmin co cneg cC cA cmin
    co wceq cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB
    cmin co cc0 wne wa wa cA cc wcel cA cB cmin co cC cB cmin co cdiv co cr
    wcel cA cc wcel cB cc wcel cC cc wcel w3a cA cc wcel cA cB cmin co cc0
    wne cC cB cmin co cc0 wne wa cA cc wcel cB cc wcel cC cc wcel simp1
    adantr adantr cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne
    cC cB cmin co cc0 wne wa wa cC cc wcel cA cB cmin co cC cB cmin co cdiv
    co cr wcel cA cc wcel cB cc wcel cC cc wcel w3a cC cc wcel cA cB cmin co
    cc0 wne cC cB cmin co cc0 wne wa cA cc wcel cB cc wcel cC cc wcel simp3
    adantr adantr cA cC negsubdi2 syl2anc cA cc wcel cB cc wcel cC cc wcel
    w3a cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA cB cmin co cC cB
    cmin co cdiv co cr wcel wa cA cc wcel cB cc wcel cA cB cmin co cneg cB cA
    cmin co wceq cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne
    cC cB cmin co cc0 wne wa wa cA cc wcel cA cB cmin co cC cB cmin co cdiv
    co cr wcel cA cc wcel cB cc wcel cC cc wcel w3a cA cc wcel cA cB cmin co
    cc0 wne cC cB cmin co cc0 wne wa cA cc wcel cB cc wcel cC cc wcel simp1
    adantr adantr cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne
    cC cB cmin co cc0 wne wa wa cB cc wcel cA cB cmin co cC cB cmin co cdiv
    co cr wcel cA cc wcel cB cc wcel cC cc wcel w3a cB cc wcel cA cB cmin co
    cc0 wne cC cB cmin co cc0 wne wa cA cc wcel cB cc wcel cC cc wcel simp2
    adantr adantr cA cB negsubdi2 syl2anc oveq12d cA cc wcel cB cc wcel cC cc
    wcel w3a cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA cB cmin co
    cC cB cmin co cdiv co cr wcel wa cA cB cmin co cC cB cmin co cmin co cA
    cB cmin co cdiv co cA cC cmin co cA cB cmin co cdiv co c1 cC cB cmin co
    cA cB cmin co cdiv co cmin co cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA cB cmin co cC cB cmin co
    cdiv co cr wcel wa cA cB cmin co cC cB cmin co cmin co cA cC cmin co cA
    cB cmin co cdiv cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0
    wne cC cB cmin co cc0 wne wa wa cA cB cmin co cC cB cmin co cdiv co cr
    wcel wa cA cc wcel cC cc wcel cB cc wcel cA cB cmin co cC cB cmin co cmin
    co cA cC cmin co wceq cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co
    cc0 wne cC cB cmin co cc0 wne wa wa cA cc wcel cA cB cmin co cC cB cmin
    co cdiv co cr wcel cA cc wcel cB cc wcel cC cc wcel w3a cA cc wcel cA cB
    cmin co cc0 wne cC cB cmin co cc0 wne wa cA cc wcel cB cc wcel cC cc wcel
    simp1 adantr adantr cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co
    cc0 wne cC cB cmin co cc0 wne wa wa cC cc wcel cA cB cmin co cC cB cmin
    co cdiv co cr wcel cA cc wcel cB cc wcel cC cc wcel w3a cC cc wcel cA cB
    cmin co cc0 wne cC cB cmin co cc0 wne wa cA cc wcel cB cc wcel cC cc wcel
    simp3 adantr adantr cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co
    cc0 wne cC cB cmin co cc0 wne wa wa cB cc wcel cA cB cmin co cC cB cmin
    co cdiv co cr wcel cA cc wcel cB cc wcel cC cc wcel w3a cB cc wcel cA cB
    cmin co cc0 wne cC cB cmin co cc0 wne wa cA cc wcel cB cc wcel cC cc wcel
    simp2 adantr adantr cA cC cB nnncan2 syl3anc oveq1d cA cc wcel cB cc wcel
    cC cc wcel w3a cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA cB
    cmin co cC cB cmin co cdiv co cr wcel wa cA cB cmin co cC cB cmin co cmin
    co cA cB cmin co cdiv co cA cB cmin co cA cB cmin co cdiv co cC cB cmin
    co cA cB cmin co cdiv co cmin co c1 cC cB cmin co cA cB cmin co cdiv co
    cmin co cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB
    cmin co cc0 wne wa wa cA cB cmin co cC cB cmin co cdiv co cr wcel wa cA
    cB cmin co cc wcel cC cB cmin co cc wcel cA cB cmin co cc wcel cA cB cmin
    co cc0 wne wa cA cB cmin co cC cB cmin co cmin co cA cB cmin co cdiv co
    cA cB cmin co cA cB cmin co cdiv co cC cB cmin co cA cB cmin co cdiv co
    cmin co wceq cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne
    cC cB cmin co cc0 wne wa wa cA cB cmin co cC cB cmin co cdiv co cr wcel
    wa cA cB cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB
    cmin co cc0 wne wa wa cA cc wcel cA cB cmin co cC cB cmin co cdiv co cr
    wcel cA cc wcel cB cc wcel cC cc wcel w3a cA cc wcel cA cB cmin co cc0
    wne cC cB cmin co cc0 wne wa cA cc wcel cB cc wcel cC cc wcel simp1
    adantr adantr cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne
    cC cB cmin co cc0 wne wa wa cB cc wcel cA cB cmin co cC cB cmin co cdiv
    co cr wcel cA cc wcel cB cc wcel cC cc wcel w3a cB cc wcel cA cB cmin co
    cc0 wne cC cB cmin co cc0 wne wa cA cc wcel cB cc wcel cC cc wcel simp2
    adantr adantr subcld cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co
    cc0 wne cC cB cmin co cc0 wne wa wa cA cB cmin co cC cB cmin co cdiv co
    cr wcel wa cC cB cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0
    wne cC cB cmin co cc0 wne wa wa cC cc wcel cA cB cmin co cC cB cmin co
    cdiv co cr wcel cA cc wcel cB cc wcel cC cc wcel w3a cC cc wcel cA cB
    cmin co cc0 wne cC cB cmin co cc0 wne wa cA cc wcel cB cc wcel cC cc wcel
    simp3 adantr adantr cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co
    cc0 wne cC cB cmin co cc0 wne wa wa cB cc wcel cA cB cmin co cC cB cmin
    co cdiv co cr wcel cA cc wcel cB cc wcel cC cc wcel w3a cB cc wcel cA cB
    cmin co cc0 wne cC cB cmin co cc0 wne wa cA cc wcel cB cc wcel cC cc wcel
    simp2 adantr adantr subcld cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA cB cmin co cC cB cmin co
    cdiv co cr wcel wa cA cB cmin co cc wcel cA cB cmin co cc0 wne cA cc wcel
    cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa
    wa cA cB cmin co cC cB cmin co cdiv co cr wcel wa cA cB cA cc wcel cB cc
    wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA
    cc wcel cA cB cmin co cC cB cmin co cdiv co cr wcel cA cc wcel cB cc wcel
    cC cc wcel w3a cA cc wcel cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa
    cA cc wcel cB cc wcel cC cc wcel simp1 adantr adantr cA cc wcel cB cc
    wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa wa cB
    cc wcel cA cB cmin co cC cB cmin co cdiv co cr wcel cA cc wcel cB cc wcel
    cC cc wcel w3a cB cc wcel cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa
    cA cc wcel cB cc wcel cC cc wcel simp2 adantr adantr subcld cA cc wcel cB
    cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa wa
    cA cB cmin co cc0 wne cA cB cmin co cC cB cmin co cdiv co cr wcel cA cB
    cmin co cc0 wne cC cB cmin co cc0 wne wa cA cB cmin co cc0 wne cA cc wcel
    cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB cmin co cc0 wne
    simpl adantl adantr jca cA cB cmin co cC cB cmin co cA cB cmin co
    divsubdir syl3anc cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0
    wne cC cB cmin co cc0 wne wa wa cA cB cmin co cC cB cmin co cdiv co cr
    wcel wa cA cB cmin co cA cB cmin co cdiv co c1 cC cB cmin co cA cB cmin
    co cdiv co cmin cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0
    wne cC cB cmin co cc0 wne wa wa cA cB cmin co cC cB cmin co cdiv co cr
    wcel wa cA cB cmin co cc wcel cA cB cmin co cc0 wne cA cB cmin co cA cB
    cmin co cdiv co c1 wceq cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin
    co cc0 wne cC cB cmin co cc0 wne wa wa cA cB cmin co cC cB cmin co cdiv
    co cr wcel wa cA cB cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co
    cc0 wne cC cB cmin co cc0 wne wa wa cA cc wcel cA cB cmin co cC cB cmin
    co cdiv co cr wcel cA cc wcel cB cc wcel cC cc wcel w3a cA cc wcel cA cB
    cmin co cc0 wne cC cB cmin co cc0 wne wa cA cc wcel cB cc wcel cC cc wcel
    simp1 adantr adantr cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co
    cc0 wne cC cB cmin co cc0 wne wa wa cB cc wcel cA cB cmin co cC cB cmin
    co cdiv co cr wcel cA cc wcel cB cc wcel cC cc wcel w3a cB cc wcel cA cB
    cmin co cc0 wne cC cB cmin co cc0 wne wa cA cc wcel cB cc wcel cC cc wcel
    simp2 adantr adantr subcld cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA cB cmin co cc0 wne cA cB
    cmin co cC cB cmin co cdiv co cr wcel cA cB cmin co cc0 wne cC cB cmin co
    cc0 wne wa cA cB cmin co cc0 wne cA cc wcel cB cc wcel cC cc wcel w3a cA
    cB cmin co cc0 wne cC cB cmin co cc0 wne simpl adantl adantr cA cB cmin
    co divid syl2anc oveq1d eqtrd eqtr3d 3eqtr3d cA cc wcel cB cc wcel cC cc
    wcel w3a cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA cB cmin co
    cC cB cmin co cdiv co cr wcel wa c1 cr wcel cC cB cmin co cA cB cmin co
    cdiv co cr wcel c1 cC cB cmin co cA cB cmin co cdiv co cmin co cr wcel c1
    cr wcel cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB
    cmin co cc0 wne wa wa cA cB cmin co cC cB cmin co cdiv co cr wcel wa 1re
    a1i cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB cmin
    co cc0 wne wa wa cA cB cmin co cC cB cmin co cdiv co cr wcel wa cA cB
    cmin co cC cB cmin co cdiv co cr wcel cC cB cmin co cA cB cmin co cdiv co
    cr wcel cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB
    cmin co cc0 wne wa wa cA cB cmin co cC cB cmin co cdiv co cr wcel simpr
    cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB cmin co
    cc0 wne wa wa cA cB cmin co cC cB cmin co cdiv co cr wcel wa cA cB cmin
    co cc wcel cA cB cmin co cc0 wne wa cC cB cmin co cc wcel cC cB cmin co
    cc0 wne wa wa cA cB cmin co cC cB cmin co cdiv co cr wcel cC cB cmin co
    cA cB cmin co cdiv co cr wcel wi cA cc wcel cB cc wcel cC cc wcel w3a cA
    cB cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA cB cmin co cC cB cmin
    co cdiv co cr wcel wa cA cB cmin co cc wcel cA cB cmin co cc0 wne wa cC
    cB cmin co cc wcel cC cB cmin co cc0 wne wa cA cc wcel cB cc wcel cC cc
    wcel w3a cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA cB cmin co
    cC cB cmin co cdiv co cr wcel wa cA cB cmin co cc wcel cA cB cmin co cc0
    wne cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB cmin
    co cc0 wne wa wa cA cB cmin co cC cB cmin co cdiv co cr wcel wa cA cB cA
    cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB cmin co cc0
    wne wa wa cA cc wcel cA cB cmin co cC cB cmin co cdiv co cr wcel cA cc
    wcel cB cc wcel cC cc wcel w3a cA cc wcel cA cB cmin co cc0 wne cC cB
    cmin co cc0 wne wa cA cc wcel cB cc wcel cC cc wcel simp1 adantr adantr
    cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB cmin co
    cc0 wne wa wa cB cc wcel cA cB cmin co cC cB cmin co cdiv co cr wcel cA
    cc wcel cB cc wcel cC cc wcel w3a cB cc wcel cA cB cmin co cc0 wne cC cB
    cmin co cc0 wne wa cA cc wcel cB cc wcel cC cc wcel simp2 adantr adantr
    subcld cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB
    cmin co cc0 wne wa wa cA cB cmin co cc0 wne cA cB cmin co cC cB cmin co
    cdiv co cr wcel cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa cA cB cmin
    co cc0 wne cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC
    cB cmin co cc0 wne simpl adantl adantr jca cA cc wcel cB cc wcel cC cc
    wcel w3a cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA cB cmin co
    cC cB cmin co cdiv co cr wcel wa cC cB cmin co cc wcel cC cB cmin co cc0
    wne cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB cmin
    co cc0 wne wa wa cA cB cmin co cC cB cmin co cdiv co cr wcel wa cC cB cA
    cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB cmin co cc0
    wne wa wa cC cc wcel cA cB cmin co cC cB cmin co cdiv co cr wcel cA cc
    wcel cB cc wcel cC cc wcel w3a cC cc wcel cA cB cmin co cc0 wne cC cB
    cmin co cc0 wne wa cA cc wcel cB cc wcel cC cc wcel simp3 adantr adantr
    cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB cmin co
    cc0 wne wa wa cB cc wcel cA cB cmin co cC cB cmin co cdiv co cr wcel cA
    cc wcel cB cc wcel cC cc wcel w3a cB cc wcel cA cB cmin co cc0 wne cC cB
    cmin co cc0 wne wa cA cc wcel cB cc wcel cC cc wcel simp2 adantr adantr
    subcld cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB
    cmin co cc0 wne wa wa cC cB cmin co cc0 wne cA cB cmin co cC cB cmin co
    cdiv co cr wcel cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa cC cB cmin
    co cc0 wne cA cc wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC
    cB cmin co cc0 wne simpr adantl adantr jca jca cA cB cmin co cC cB cmin
    co gtrirec syl mpd c1 cC cB cmin co cA cB cmin co cdiv co resubcl syl2anc
    eqeltrd ex $.

  gtrirotate $p |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( ( ( -. A = B /\ -. B = C ) /\ -. A = C ) /\ -. ( ( C - A ) / ( B - A ) ) e. RR ) -> ( ( ( -. B = C /\ -. C = A ) /\ -. B = A ) /\ -. ( ( A - B ) / ( C - B ) ) e. RR ) ) ) $=
    cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC
    wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa cB cC wceq
    wn cC cA wceq wn wa cB cA wceq wn wa cA cB cmin co cC cB cmin co cdiv co
    cr wcel wn wa cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC
    wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel
    wn wa wa cB cC wceq wn cC cA wceq wn wa cB cA wceq wn wa cA cB cmin co cC
    cB cmin co cdiv co cr wcel wn cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co
    cdiv co cr wcel wn wa wa cB cC wceq wn cC cA wceq wn cB cA wceq wn cA cc
    wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq
    wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa cA cB wceq wn
    cB cC wceq wn cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC
    wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel
    wn wa wa cA cB wceq wn cB cC wceq wn wa cA cC wceq wn cA cc wcel cB cc
    wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA
    cmin co cB cA cmin co cdiv co cr wcel wn wa wa cA cB wceq wn cB cC wceq
    wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn cA
    cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC
    wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa simpr simpld
    simpld simprd cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC
    wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel
    wn wa wa cC cA cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC
    wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel
    wn wa wa cA cC cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC
    wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel
    wn wa wa cA cC cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC
    wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel
    wn wa wa cA cB wceq wn cB cC wceq wn wa cA cC wceq wn cA cc wcel cB cc
    wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA
    cmin co cB cA cmin co cdiv co cr wcel wn wa wa cA cB wceq wn cB cC wceq
    wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn cA
    cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC
    wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa simpr simpld
    simprd neqned necomd neneqd cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co
    cdiv co cr wcel wn wa wa cB cA cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co
    cdiv co cr wcel wn wa wa cA cB cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co
    cdiv co cr wcel wn wa wa cA cB cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co
    cdiv co cr wcel wn wa wa cA cB wceq wn cB cC wceq wn cA cc wcel cB cc
    wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA
    cmin co cB cA cmin co cdiv co cr wcel wn wa wa cA cB wceq wn cB cC wceq
    wn wa cA cC wceq wn cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB
    cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr
    wcel wn wa wa cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin
    co cB cA cmin co cdiv co cr wcel wn cA cc wcel cB cc wcel cC cc wcel w3a
    cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin
    co cdiv co cr wcel wn wa simpr simpld simpld simpld neqned necomd neneqd
    jca31 cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa
    cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa cC
    cA cmin co cB cA cmin co cdiv co cr wcel wn cA cB cmin co cC cB cmin co
    cdiv co cr wcel wn cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB
    cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr
    wcel wn wa wa cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin
    co cB cA cmin co cdiv co cr wcel wn cA cc wcel cB cc wcel cC cc wcel w3a
    cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin
    co cdiv co cr wcel wn wa simpr simprd cA cc wcel cB cc wcel cC cc wcel
    w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA
    cmin co cdiv co cr wcel wn wa wa cA cB cmin co cC cB cmin co cdiv co cr
    wcel cC cA cmin co cB cA cmin co cdiv co cr wcel cA cc wcel cB cc wcel cC
    cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co
    cB cA cmin co cdiv co cr wcel wn wa wa cA cc wcel cB cc wcel cC cc wcel
    w3a cA cB cmin co cc0 wne cC cB cmin co cc0 wne wa wa cA cB cmin co cC cB
    cmin co cdiv co cr wcel cC cA cmin co cB cA cmin co cdiv co cr wcel wi cA
    cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC
    wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa cA cc
    wcel cB cc wcel cC cc wcel w3a cA cB cmin co cc0 wne cC cB cmin co cc0
    wne wa cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn
    wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa
    simpl cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa
    cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa cA
    cB cmin co cc0 wne cC cB cmin co cc0 wne cA cc wcel cB cc wcel cC cc wcel
    w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA
    cmin co cdiv co cr wcel wn wa wa cA cB cmin co cc0 wne cA cB wne cA cc
    wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq
    wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa cA cB cA cc
    wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq
    wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa cA cB wceq wn
    cB cC wceq wn cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC
    wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel
    wn wa wa cA cB wceq wn cB cC wceq wn wa cA cC wceq wn cA cc wcel cB cc
    wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA
    cmin co cB cA cmin co cdiv co cr wcel wn wa wa cA cB wceq wn cB cC wceq
    wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn cA
    cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC
    wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa simpr simpld
    simpld simpld neqned cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn
    cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr
    wcel wn wa wa cA cB cmin co cc0 cA cB cA cc wcel cB cc wcel cC cc wcel
    w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA
    cmin co cdiv co cr wcel wn wa wa cA cB cA cc wcel cB cc wcel cC cc wcel
    w3a cA cc wcel cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin
    co cB cA cmin co cdiv co cr wcel wn wa cA cc wcel cB cc wcel cC cc wcel
    simp1 adantr cA cc wcel cB cc wcel cC cc wcel w3a cB cc wcel cA cB wceq
    wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co
    cr wcel wn wa cA cc wcel cB cc wcel cC cc wcel simp2 adantr subeq0ad
    necon3bid mpbird cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC
    wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel
    wn wa wa cC cB cmin co cc0 wne cC cB wne cA cc wcel cB cc wcel cC cc wcel
    w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA
    cmin co cdiv co cr wcel wn wa wa cC cB cA cc wcel cB cc wcel cC cc wcel
    w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA
    cmin co cdiv co cr wcel wn wa wa cC cB cA cc wcel cB cc wcel cC cc wcel
    w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA
    cmin co cdiv co cr wcel wn wa wa cB cC cA cc wcel cB cc wcel cC cc wcel
    w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA
    cmin co cdiv co cr wcel wn wa wa cB cC cA cc wcel cB cc wcel cC cc wcel
    w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA
    cmin co cdiv co cr wcel wn wa wa cA cB wceq wn cB cC wceq wn cA cc wcel
    cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa
    cC cA cmin co cB cA cmin co cdiv co cr wcel wn wa wa cA cB wceq wn cB cC
    wceq wn wa cA cC wceq wn cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq
    wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co
    cr wcel wn wa wa cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA
    cmin co cB cA cmin co cdiv co cr wcel wn cA cc wcel cB cc wcel cC cc wcel
    w3a cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA
    cmin co cdiv co cr wcel wn wa simpr simpld simpld simprd neqned necomd
    neneqd neqned cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cB cC
    wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr wcel
    wn wa wa cC cB cmin co cc0 cC cB cA cc wcel cB cc wcel cC cc wcel w3a cA
    cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co
    cdiv co cr wcel wn wa wa cC cB cA cc wcel cB cc wcel cC cc wcel w3a cC cc
    wcel cA cB wceq wn cB cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA
    cmin co cdiv co cr wcel wn wa cA cc wcel cB cc wcel cC cc wcel simp3
    adantr cA cc wcel cB cc wcel cC cc wcel w3a cB cc wcel cA cB wceq wn cB
    cC wceq wn wa cA cC wceq wn wa cC cA cmin co cB cA cmin co cdiv co cr
    wcel wn wa cA cc wcel cB cc wcel cC cc wcel simp2 adantr subeq0ad
    necon3bid mpbird jca jca cA cB cC gtricol syl con3d mpd jca ex $.

  gangval $p |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) -> ( A ang B ) = ( Im ` ( log ` ( B / A ) ) ) ) $=
    vx vy cA cB cang vx vy df-ang angval $.

  gangrec $p |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) -> ( B ang A ) = ( Im ` ( log ` ( 1 / ( B / A ) ) ) ) ) $=
    cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cang co cA cB
    cdiv co clog cfv cim cfv c1 cB cA cdiv co cdiv co clog cfv cim cfv cB cc
    wcel cB cc0 wne wa cA cc wcel cA cc0 wne wa cB cA cang co cA cB cdiv co
    clog cfv cim cfv wceq vx vy cB cA cang vx vy df-ang angval ancoms cA cc
    wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cB cdiv co clog cfv c1
    cB cA cdiv co cdiv co clog cfv cim cA cc wcel cA cc0 wne wa cB cc wcel cB
    cc0 wne wa wa cA cB cdiv co c1 cB cA cdiv co cdiv co clog cA cc wcel cA
    cc0 wne wa cB cc wcel cB cc0 wne wa wa c1 cB cA cdiv co cdiv co cA cB
    cdiv co cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cc wcel
    cB cc0 wne wa cA cc wcel cA cc0 wne wa wa c1 cB cA cdiv co cdiv co cA cB
    cdiv co wceq cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cc
    wcel cB cc0 wne wa cA cc wcel cA cc0 wne wa cA cc wcel cA cc0 wne wa cB
    cc wcel cB cc0 wne wa simpr cA cc wcel cA cc0 wne wa cB cc wcel cB cc0
    wne wa simpl jca cB cA recdiv syl eqcomd fveq2d fveq2d eqtrd $.

  gangsym $p |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) -> ( abs ` ( A ang B ) ) = ( abs ` ( B ang A ) ) ) $=
    cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co clog
    cfv cim cfv cabs cfv c1 cB cA cdiv co cdiv co clog cfv cim cfv cabs cfv
    cA cB cang co cabs cfv cB cA cang co cabs cfv cA cc wcel cA cc0 wne wa cB
    cc wcel cB cc0 wne wa wa cB cA cdiv co cneg crp wcel cB cA cdiv co clog
    cfv cim cfv cabs cfv c1 cB cA cdiv co cdiv co clog cfv cim cfv cabs cfv
    wceq cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co
    cneg crp wcel wa cB cA cdiv co clog cfv cim cfv cabs cfv cpi cabs cfv c1
    cB cA cdiv co cdiv co clog cfv cim cfv cabs cfv cA cc wcel cA cc0 wne wa
    cB cc wcel cB cc0 wne wa wa cB cA cdiv co cneg crp wcel wa cB cA cdiv co
    clog cfv cim cfv cpi cabs cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne
    wa wa cB cA cdiv co cneg crp wcel wa cB cA cdiv co cneg crp wcel cB cA
    cdiv co clog cfv cim cfv cpi wceq cA cc wcel cA cc0 wne wa cB cc wcel cB
    cc0 wne wa wa cB cA cdiv co cneg crp wcel simpr cA cc wcel cA cc0 wne wa
    cB cc wcel cB cc0 wne wa wa cB cA cdiv co cneg crp wcel wa cB cA cdiv co
    cc wcel cB cA cdiv co cc0 wne cB cA cdiv co cneg crp wcel cB cA cdiv co
    clog cfv cim cfv cpi wceq wb cA cc wcel cA cc0 wne wa cB cc wcel cB cc0
    wne wa wa cB cA cdiv co cc wcel cB cA cdiv co cneg crp wcel cA cc wcel cA
    cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cc wcel cA cc wcel cA cc0 wne
    cB cA cdiv co cc wcel cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa
    wa cB cc wcel cB cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne
    wa simpr simpld cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cA
    cc wcel cA cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa
    simpl simpld cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cc
    wcel cA cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa simpl
    simprd cB cA divcl syl3anc adantr cA cc wcel cA cc0 wne wa cB cc wcel cB
    cc0 wne wa wa cB cA cdiv co cc0 wne cB cA cdiv co cneg crp wcel cA cc
    wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cc wcel cB cc0 wne wa
    cA cc wcel cA cc0 wne wa wa cB cA cdiv co cc0 wne cA cc wcel cA cc0 wne
    wa cB cc wcel cB cc0 wne wa wa cB cc wcel cB cc0 wne wa cA cc wcel cA cc0
    wne wa cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa simpr cA cc wcel
    cA cc0 wne wa cB cc wcel cB cc0 wne wa simpl jca cB cA divne0 syl adantr
    cB cA cdiv co lognegb syl2anc mpbid fveq2d cA cc wcel cA cc0 wne wa cB cc
    wcel cB cc0 wne wa wa cB cA cdiv co cneg crp wcel wa c1 cB cA cdiv co
    cdiv co clog cfv cim cfv cpi cabs cA cc wcel cA cc0 wne wa cB cc wcel cB
    cc0 wne wa wa cB cA cdiv co cneg crp wcel wa c1 cB cA cdiv co cdiv co
    cneg crp wcel c1 cB cA cdiv co cdiv co clog cfv cim cfv cpi wceq cA cc
    wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co cneg crp
    wcel wa c1 cB cA cdiv co cneg cdiv co c1 cB cA cdiv co cdiv co cneg crp
    cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co cneg
    crp wcel wa c1 cB cA cdiv co cdiv co cneg c1 cB cA cdiv co cneg cdiv co
    cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co cneg
    crp wcel wa c1 cc wcel cB cA cdiv co cc wcel cB cA cdiv co cc0 wne c1 cB
    cA cdiv co cdiv co cneg c1 cB cA cdiv co cneg cdiv co wceq c1 cc wcel cA
    cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co cneg crp
    wcel wa ax-1cn a1i cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa
    cB cA cdiv co cc wcel cB cA cdiv co cneg crp wcel cA cc wcel cA cc0 wne
    wa cB cc wcel cB cc0 wne wa wa cB cc wcel cA cc wcel cA cc0 wne cB cA
    cdiv co cc wcel cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB
    cc wcel cB cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa
    simpr simpld cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cc
    wcel cA cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa simpl
    simpld cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cc wcel cA
    cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa simpl simprd cB
    cA divcl syl3anc adantr cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa
    wa cB cA cdiv co cc0 wne cB cA cdiv co cneg crp wcel cA cc wcel cA cc0
    wne wa cB cc wcel cB cc0 wne wa wa cB cc wcel cB cc0 wne wa cA cc wcel cA
    cc0 wne wa wa cB cA cdiv co cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel
    cB cc0 wne wa wa cB cc wcel cB cc0 wne wa cA cc wcel cA cc0 wne wa cA cc
    wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa simpr cA cc wcel cA cc0 wne
    wa cB cc wcel cB cc0 wne wa simpl jca cB cA divne0 syl adantr c1 cB cA
    cdiv co divneg2 syl3anc eqcomd cA cc wcel cA cc0 wne wa cB cc wcel cB cc0
    wne wa wa cB cA cdiv co cneg crp wcel wa cB cA cdiv co cneg crp wcel c1
    cB cA cdiv co cneg cdiv co crp wcel cA cc wcel cA cc0 wne wa cB cc wcel
    cB cc0 wne wa wa cB cA cdiv co cneg crp wcel simpr cB cA cdiv co cneg
    rpreccl syl eqeltrrd cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa
    cB cA cdiv co cneg crp wcel wa c1 cB cA cdiv co cdiv co cc wcel c1 cB cA
    cdiv co cdiv co cc0 wne c1 cB cA cdiv co cdiv co cneg crp wcel c1 cB cA
    cdiv co cdiv co clog cfv cim cfv cpi wceq wb cA cc wcel cA cc0 wne wa cB
    cc wcel cB cc0 wne wa wa cB cA cdiv co cneg crp wcel wa cB cA cdiv co cA
    cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co cc wcel
    cB cA cdiv co cneg crp wcel cA cc wcel cA cc0 wne wa cB cc wcel cB cc0
    wne wa wa cB cc wcel cA cc wcel cA cc0 wne cB cA cdiv co cc wcel cA cc
    wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cc wcel cB cc0 wne cA
    cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa simpr simpld cA cc wcel cA
    cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cc wcel cA cc0 wne cA cc wcel
    cA cc0 wne wa cB cc wcel cB cc0 wne wa simpl simpld cA cc wcel cA cc0 wne
    wa cB cc wcel cB cc0 wne wa wa cA cc wcel cA cc0 wne cA cc wcel cA cc0
    wne wa cB cc wcel cB cc0 wne wa simpl simprd cB cA divcl syl3anc adantr
    cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co cc0
    wne cB cA cdiv co cneg crp wcel cA cc wcel cA cc0 wne wa cB cc wcel cB
    cc0 wne wa wa cB cc wcel cB cc0 wne wa cA cc wcel cA cc0 wne wa wa cB cA
    cdiv co cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB
    cc wcel cB cc0 wne wa cA cc wcel cA cc0 wne wa cA cc wcel cA cc0 wne wa
    cB cc wcel cB cc0 wne wa simpr cA cc wcel cA cc0 wne wa cB cc wcel cB cc0
    wne wa simpl jca cB cA divne0 syl adantr reccld cA cc wcel cA cc0 wne wa
    cB cc wcel cB cc0 wne wa wa cB cA cdiv co cneg crp wcel wa cB cA cdiv co
    cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co cc
    wcel cB cA cdiv co cneg crp wcel cA cc wcel cA cc0 wne wa cB cc wcel cB
    cc0 wne wa wa cB cc wcel cA cc wcel cA cc0 wne cB cA cdiv co cc wcel cA
    cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cc wcel cB cc0 wne
    cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa simpr simpld cA cc wcel
    cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cc wcel cA cc0 wne cA cc
    wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa simpl simpld cA cc wcel cA
    cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cc wcel cA cc0 wne cA cc wcel
    cA cc0 wne wa cB cc wcel cB cc0 wne wa simpl simprd cB cA divcl syl3anc
    adantr cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co
    cc0 wne cB cA cdiv co cneg crp wcel cA cc wcel cA cc0 wne wa cB cc wcel
    cB cc0 wne wa wa cB cc wcel cB cc0 wne wa cA cc wcel cA cc0 wne wa wa cB
    cA cdiv co cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa
    cB cc wcel cB cc0 wne wa cA cc wcel cA cc0 wne wa cA cc wcel cA cc0 wne
    wa cB cc wcel cB cc0 wne wa simpr cA cc wcel cA cc0 wne wa cB cc wcel cB
    cc0 wne wa simpl jca cB cA divne0 syl adantr recne0d c1 cB cA cdiv co
    cdiv co lognegb syl2anc mpbid fveq2d eqtr4d cA cc wcel cA cc0 wne wa cB
    cc wcel cB cc0 wne wa wa cB cA cdiv co cneg crp wcel wn wa c1 cB cA cdiv
    co cdiv co clog cfv cim cfv cabs cfv cB cA cdiv co clog cfv cim cfv cabs
    cfv cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co
    cneg crp wcel wn wa c1 cB cA cdiv co cdiv co clog cfv cim cfv cabs cfv cB
    cA cdiv co clog cfv cim cfv cneg cabs cfv cB cA cdiv co clog cfv cim cfv
    cabs cfv cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv
    co cneg crp wcel wn wa c1 cB cA cdiv co cdiv co clog cfv cim cfv cB cA
    cdiv co clog cfv cim cfv cneg cabs cA cc wcel cA cc0 wne wa cB cc wcel cB
    cc0 wne wa wa cB cA cdiv co cneg crp wcel wn wa cB cA cdiv co cA cc wcel
    cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co cc wcel cB cA
    cdiv co cneg crp wcel wn cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne
    wa wa cB cc wcel cA cc wcel cA cc0 wne cB cA cdiv co cc wcel cA cc wcel
    cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cc wcel cB cc0 wne cA cc
    wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa simpr simpld cA cc wcel cA
    cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cc wcel cA cc0 wne cA cc wcel
    cA cc0 wne wa cB cc wcel cB cc0 wne wa simpl simpld cA cc wcel cA cc0 wne
    wa cB cc wcel cB cc0 wne wa wa cA cc wcel cA cc0 wne cA cc wcel cA cc0
    wne wa cB cc wcel cB cc0 wne wa simpl simprd cB cA divcl syl3anc adantr
    cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co cc0
    wne cB cA cdiv co cneg crp wcel wn cA cc wcel cA cc0 wne wa cB cc wcel cB
    cc0 wne wa wa cB cc wcel cB cc0 wne wa cA cc wcel cA cc0 wne wa wa cB cA
    cdiv co cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB
    cc wcel cB cc0 wne wa cA cc wcel cA cc0 wne wa cA cc wcel cA cc0 wne wa
    cB cc wcel cB cc0 wne wa simpr cA cc wcel cA cc0 wne wa cB cc wcel cB cc0
    wne wa simpl jca cB cA divne0 syl adantr cA cc wcel cA cc0 wne wa cB cc
    wcel cB cc0 wne wa wa cB cA cdiv co cneg crp wcel wn simpr arginv fveq2d
    cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co cneg
    crp wcel wn wa cB cA cdiv co clog cfv cim cfv cc wcel cB cA cdiv co clog
    cfv cim cfv cneg cabs cfv cB cA cdiv co clog cfv cim cfv cabs cfv wceq cA
    cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co cneg crp
    wcel wn wa cB cA cdiv co clog cfv cim cfv cr wcel cB cA cdiv co clog cfv
    cim cfv cc wcel cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB
    cA cdiv co cneg crp wcel wn wa cB cA cdiv co clog cfv cc wcel cB cA cdiv
    co clog cfv cim cfv cr wcel cA cc wcel cA cc0 wne wa cB cc wcel cB cc0
    wne wa wa cB cA cdiv co cneg crp wcel wn wa cB cA cdiv co cA cc wcel cA
    cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co cc wcel cB cA cdiv
    co cneg crp wcel wn cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa
    cB cc wcel cA cc wcel cA cc0 wne cB cA cdiv co cc wcel cA cc wcel cA cc0
    wne wa cB cc wcel cB cc0 wne wa wa cB cc wcel cB cc0 wne cA cc wcel cA
    cc0 wne wa cB cc wcel cB cc0 wne wa simpr simpld cA cc wcel cA cc0 wne wa
    cB cc wcel cB cc0 wne wa wa cA cc wcel cA cc0 wne cA cc wcel cA cc0 wne
    wa cB cc wcel cB cc0 wne wa simpl simpld cA cc wcel cA cc0 wne wa cB cc
    wcel cB cc0 wne wa wa cA cc wcel cA cc0 wne cA cc wcel cA cc0 wne wa cB
    cc wcel cB cc0 wne wa simpl simprd cB cA divcl syl3anc adantr cA cc wcel
    cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co cc0 wne cB cA
    cdiv co cneg crp wcel wn cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne
    wa wa cB cc wcel cB cc0 wne wa cA cc wcel cA cc0 wne wa wa cB cA cdiv co
    cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cc wcel
    cB cc0 wne wa cA cc wcel cA cc0 wne wa cA cc wcel cA cc0 wne wa cB cc
    wcel cB cc0 wne wa simpr cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne
    wa simpl jca cB cA divne0 syl adantr logcld cB cA cdiv co clog cfv imcl
    syl cB cA cdiv co clog cfv cim cfv recn syl cB cA cdiv co clog cfv cim
    cfv absneg syl eqtrd eqcomd pm2.61dan cA cc wcel cA cc0 wne wa cB cc wcel
    cB cc0 wne wa wa cA cB cang co cB cA cdiv co clog cfv cim cfv cabs vx vy
    cA cB cang vx vy df-ang angval fveq2d cA cc wcel cA cc0 wne wa cB cc wcel
    cB cc0 wne wa wa cB cA cang co c1 cB cA cdiv co cdiv co clog cfv cim cfv
    cabs cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cang co
    cA cB cdiv co clog cfv cim cfv c1 cB cA cdiv co cdiv co clog cfv cim cfv
    cB cc wcel cB cc0 wne wa cA cc wcel cA cc0 wne wa cB cA cang co cA cB
    cdiv co clog cfv cim cfv wceq vx vy cB cA cang vx vy df-ang angval ancoms
    cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cB cdiv co clog
    cfv c1 cB cA cdiv co cdiv co clog cfv cim cA cc wcel cA cc0 wne wa cB cc
    wcel cB cc0 wne wa wa cA cB cdiv co c1 cB cA cdiv co cdiv co clog cA cc
    wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa c1 cB cA cdiv co cdiv co
    cA cB cdiv co cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cc
    wcel cB cc0 wne wa cA cc wcel cA cc0 wne wa wa c1 cB cA cdiv co cdiv co
    cA cB cdiv co wceq cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa
    cB cc wcel cB cc0 wne wa cA cc wcel cA cc0 wne wa cA cc wcel cA cc0 wne
    wa cB cc wcel cB cc0 wne wa simpr cA cc wcel cA cc0 wne wa cB cc wcel cB
    cc0 wne wa simpl jca cB cA recdiv syl eqcomd fveq2d fveq2d eqtrd fveq2d
    3eqtr4d $.

  gangsym3 $p |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( -. A = B /\ -. C = B ) -> ( abs ` ( ( A - B ) ang ( C - B ) ) ) = ( abs ` ( ( C - B ) ang ( A - B ) ) ) ) ) $=
    cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa cA cB
    cmin co cC cB cmin co cang co cabs cfv cC cB cmin co cA cB cmin co cang
    co cabs cfv wceq cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB
    wceq wn wa wa cA cB cmin co cc wcel cA cB cmin co cc0 wne wa cC cB cmin
    co cc wcel cC cB cmin co cc0 wne wa wa cA cB cmin co cC cB cmin co cang
    co cabs cfv cC cB cmin co cA cB cmin co cang co cabs cfv wceq cA cc wcel
    cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cA cB cmin co
    cc wcel cA cB cmin co cc0 wne wa cC cB cmin co cc wcel cC cB cmin co cc0
    wne wa cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn
    wa wa cA cB cmin co cc wcel cA cB cmin co cc0 wne cA cc wcel cB cc wcel
    cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cA cB cA cc wcel cB cc
    wcel cC cc wcel w3a cA cc wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel
    cB cc wcel cC cc wcel simp1 adantr cA cc wcel cB cc wcel cC cc wcel w3a
    cB cc wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel cB cc wcel cC cc
    wcel simp2 adantr subcld cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq
    wn cC cB wceq wn wa wa cA cB cmin co cc0 wne cA cB wne cA cc wcel cB cc
    wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cA cB cA cB wceq wn
    cC cB wceq wn wa cA cB wceq wn cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    wceq wn cC cB wceq wn simpl adantl neqned cA cc wcel cB cc wcel cC cc
    wcel w3a cA cB wceq wn cC cB wceq wn wa wa cA cB cmin co cc0 cA cB cA cc
    wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cA cB cA
    cc wcel cB cc wcel cC cc wcel w3a cA cc wcel cA cB wceq wn cC cB wceq wn
    wa cA cc wcel cB cc wcel cC cc wcel simp1 adantr cA cc wcel cB cc wcel cC
    cc wcel w3a cB cc wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel cB cc
    wcel cC cc wcel simp2 adantr subeq0ad necon3bid mpbird jca cA cc wcel cB
    cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cC cB cmin co cc
    wcel cC cB cmin co cc0 wne cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    wceq wn cC cB wceq wn wa wa cC cB cA cc wcel cB cc wcel cC cc wcel w3a cC
    cc wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel cB cc wcel cC cc wcel
    simp3 adantr cA cc wcel cB cc wcel cC cc wcel w3a cB cc wcel cA cB wceq
    wn cC cB wceq wn wa cA cc wcel cB cc wcel cC cc wcel simp2 adantr subcld
    cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cC
    cB cmin co cc0 wne cC cB wne cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    wceq wn cC cB wceq wn wa wa cC cB cA cB wceq wn cC cB wceq wn wa cC cB
    wceq wn cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn
    simpr adantl neqned cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC
    cB wceq wn wa wa cC cB cmin co cc0 cC cB cA cc wcel cB cc wcel cC cc wcel
    w3a cA cB wceq wn cC cB wceq wn wa wa cC cB cA cc wcel cB cc wcel cC cc
    wcel w3a cC cc wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel cB cc wcel
    cC cc wcel simp3 adantr cA cc wcel cB cc wcel cC cc wcel w3a cB cc wcel
    cA cB wceq wn cC cB wceq wn wa cA cc wcel cB cc wcel cC cc wcel simp2
    adantr subeq0ad necon3bid mpbird jca jca cA cB cmin co cC cB cmin co
    gangsym syl ex $.

  gcosabs $p |- ( A e. RR -> ( cos ` ( abs ` A ) ) = ( cos ` A ) ) $=
    cA cr wcel cA cabs cfv ccos cfv cA ccos cfv wceq cc0 cA cc0 cr wcel cA cr
    wcel 0re a1i cA cr wcel id cA cr wcel cc0 cA cle wbr wa cA cabs cfv cA
    ccos cA absid fveq2d cA cr wcel cA cc0 cle wbr wa cA cabs cfv ccos cfv cA
    cneg ccos cfv cA ccos cfv cA cr wcel cA cc0 cle wbr wa cA cabs cfv cA
    cneg ccos cA absnid fveq2d cA cr wcel cA cc0 cle wbr wa cA cc wcel cA
    cneg ccos cfv cA ccos cfv wceq cA cr wcel cA cc0 cle wbr wa cA cA cr wcel
    cA cc0 cle wbr simpl recnd cA cosneg syl eqtrd lecasei $.

  gangrange $p |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) -> ( abs ` ( A ang B ) ) e. ( 0 [,] _pi ) ) $=
    cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cB cang co cabs
    cfv cB cA cdiv co clog cfv cim cfv cabs cfv cc0 cpi cicc co cA cc wcel cA
    cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cB cang co cB cA cdiv co clog
    cfv cim cfv cabs cA cB gangval fveq2d cA cc wcel cA cc0 wne wa cB cc wcel
    cB cc0 wne wa wa cB cA cdiv co clog cfv cim cfv cabs cfv cc0 cpi cicc co
    wcel cB cA cdiv co clog cfv cim cfv cabs cfv cr wcel cc0 cB cA cdiv co
    clog cfv cim cfv cabs cfv cle wbr cB cA cdiv co clog cfv cim cfv cabs cfv
    cpi cle wbr cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA
    cdiv co clog cfv cim cfv cc wcel cB cA cdiv co clog cfv cim cfv cabs cfv
    cr wcel cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv
    co clog cfv cim cfv cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa
    cB cA cdiv co clog cfv cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa
    wa cB cA cdiv co cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB
    cc wcel cA cc wcel cA cc0 wne cB cA cdiv co cc wcel cA cc wcel cA cc0 wne
    wa cB cc wcel cB cc0 wne wa wa cB cc wcel cB cc0 wne cA cc wcel cA cc0
    wne wa cB cc wcel cB cc0 wne wa simpr simpld cA cc wcel cA cc0 wne wa cB
    cc wcel cB cc0 wne wa wa cA cc wcel cA cc0 wne cA cc wcel cA cc0 wne wa
    cB cc wcel cB cc0 wne wa simpl simpld cA cc wcel cA cc0 wne wa cB cc wcel
    cB cc0 wne wa wa cA cc wcel cA cc0 wne cA cc wcel cA cc0 wne wa cB cc
    wcel cB cc0 wne wa simpl simprd cB cA divcl syl3anc cA cc wcel cA cc0 wne
    wa cB cc wcel cB cc0 wne wa wa cB cc wcel cB cc0 wne wa cA cc wcel cA cc0
    wne wa wa cB cA cdiv co cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel cB
    cc0 wne wa wa cB cc wcel cB cc0 wne wa cA cc wcel cA cc0 wne wa cA cc
    wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa simpr cA cc wcel cA cc0 wne
    wa cB cc wcel cB cc0 wne wa simpl jca cB cA divne0 syl logcld imcld recnd
    cB cA cdiv co clog cfv cim cfv abscl syl cA cc wcel cA cc0 wne wa cB cc
    wcel cB cc0 wne wa wa cB cA cdiv co clog cfv cim cfv cc wcel cc0 cB cA
    cdiv co clog cfv cim cfv cabs cfv cle wbr cA cc wcel cA cc0 wne wa cB cc
    wcel cB cc0 wne wa wa cB cA cdiv co clog cfv cim cfv cA cc wcel cA cc0
    wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co clog cfv cA cc wcel cA
    cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co cA cc wcel cA cc0
    wne wa cB cc wcel cB cc0 wne wa wa cB cc wcel cA cc wcel cA cc0 wne cB cA
    cdiv co cc wcel cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB
    cc wcel cB cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa
    simpr simpld cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cc
    wcel cA cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa simpl
    simpld cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cc wcel cA
    cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa simpl simprd cB
    cA divcl syl3anc cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB
    cc wcel cB cc0 wne wa cA cc wcel cA cc0 wne wa wa cB cA cdiv co cc0 wne
    cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cc wcel cB cc0
    wne wa cA cc wcel cA cc0 wne wa cA cc wcel cA cc0 wne wa cB cc wcel cB
    cc0 wne wa simpr cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa simpl
    jca cB cA divne0 syl logcld imcld recnd cB cA cdiv co clog cfv cim cfv
    absge0 syl cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA
    cdiv co clog cfv cim cfv cabs cfv cpi cle wbr cpi cneg cB cA cdiv co clog
    cfv cim cfv cle wbr cB cA cdiv co clog cfv cim cfv cpi cle wbr cA cc wcel
    cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cpi cneg cB cA cdiv co clog cfv
    cim cfv cpi cneg cr wcel cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne
    wa wa cpi cr wcel cpi cneg cr wcel pire cpi renegcl ax-mp a1i cA cc wcel
    cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co clog cfv cA cc
    wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co cA cc wcel
    cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cc wcel cA cc wcel cA cc0
    wne cB cA cdiv co cc wcel cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne
    wa wa cB cc wcel cB cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel cB cc0
    wne wa simpr simpld cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa
    cA cc wcel cA cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa
    simpl simpld cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cc
    wcel cA cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa simpl
    simprd cB cA divcl syl3anc cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne
    wa wa cB cc wcel cB cc0 wne wa cA cc wcel cA cc0 wne wa wa cB cA cdiv co
    cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cc wcel
    cB cc0 wne wa cA cc wcel cA cc0 wne wa cA cc wcel cA cc0 wne wa cB cc
    wcel cB cc0 wne wa simpr cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne
    wa simpl jca cB cA divne0 syl logcld imcld cA cc wcel cA cc0 wne wa cB cc
    wcel cB cc0 wne wa wa cpi cneg cB cA cdiv co clog cfv cim cfv clt wbr cB
    cA cdiv co clog cfv cim cfv cpi cle wbr cA cc wcel cA cc0 wne wa cB cc
    wcel cB cc0 wne wa wa cB cA cdiv co cc wcel cB cA cdiv co cc0 wne cpi
    cneg cB cA cdiv co clog cfv cim cfv clt wbr cB cA cdiv co clog cfv cim
    cfv cpi cle wbr wa cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa
    cB cc wcel cA cc wcel cA cc0 wne cB cA cdiv co cc wcel cA cc wcel cA cc0
    wne wa cB cc wcel cB cc0 wne wa wa cB cc wcel cB cc0 wne cA cc wcel cA
    cc0 wne wa cB cc wcel cB cc0 wne wa simpr simpld cA cc wcel cA cc0 wne wa
    cB cc wcel cB cc0 wne wa wa cA cc wcel cA cc0 wne cA cc wcel cA cc0 wne
    wa cB cc wcel cB cc0 wne wa simpl simpld cA cc wcel cA cc0 wne wa cB cc
    wcel cB cc0 wne wa wa cA cc wcel cA cc0 wne cA cc wcel cA cc0 wne wa cB
    cc wcel cB cc0 wne wa simpl simprd cB cA divcl syl3anc cA cc wcel cA cc0
    wne wa cB cc wcel cB cc0 wne wa wa cB cc wcel cB cc0 wne wa cA cc wcel cA
    cc0 wne wa wa cB cA cdiv co cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel
    cB cc0 wne wa wa cB cc wcel cB cc0 wne wa cA cc wcel cA cc0 wne wa cA cc
    wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa simpr cA cc wcel cA cc0 wne
    wa cB cc wcel cB cc0 wne wa simpl jca cB cA divne0 syl cB cA cdiv co
    logimcl syl2anc simpld ltled cA cc wcel cA cc0 wne wa cB cc wcel cB cc0
    wne wa wa cpi cneg cB cA cdiv co clog cfv cim cfv clt wbr cB cA cdiv co
    clog cfv cim cfv cpi cle wbr cA cc wcel cA cc0 wne wa cB cc wcel cB cc0
    wne wa wa cB cA cdiv co cc wcel cB cA cdiv co cc0 wne cpi cneg cB cA cdiv
    co clog cfv cim cfv clt wbr cB cA cdiv co clog cfv cim cfv cpi cle wbr wa
    cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cc wcel cA cc
    wcel cA cc0 wne cB cA cdiv co cc wcel cA cc wcel cA cc0 wne wa cB cc wcel
    cB cc0 wne wa wa cB cc wcel cB cc0 wne cA cc wcel cA cc0 wne wa cB cc
    wcel cB cc0 wne wa simpr simpld cA cc wcel cA cc0 wne wa cB cc wcel cB
    cc0 wne wa wa cA cc wcel cA cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel
    cB cc0 wne wa simpl simpld cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne
    wa wa cA cc wcel cA cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel cB cc0
    wne wa simpl simprd cB cA divcl syl3anc cA cc wcel cA cc0 wne wa cB cc
    wcel cB cc0 wne wa wa cB cc wcel cB cc0 wne wa cA cc wcel cA cc0 wne wa
    wa cB cA cdiv co cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne
    wa wa cB cc wcel cB cc0 wne wa cA cc wcel cA cc0 wne wa cA cc wcel cA cc0
    wne wa cB cc wcel cB cc0 wne wa simpr cA cc wcel cA cc0 wne wa cB cc wcel
    cB cc0 wne wa simpl jca cB cA divne0 syl cB cA cdiv co logimcl syl2anc
    simprd cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cA cdiv co
    clog cfv cim cfv cr wcel cpi cr wcel cB cA cdiv co clog cfv cim cfv cabs
    cfv cpi cle wbr cpi cneg cB cA cdiv co clog cfv cim cfv cle wbr cB cA
    cdiv co clog cfv cim cfv cpi cle wbr wa wb cA cc wcel cA cc0 wne wa cB cc
    wcel cB cc0 wne wa wa cB cA cdiv co clog cfv cA cc wcel cA cc0 wne wa cB
    cc wcel cB cc0 wne wa wa cB cA cdiv co cA cc wcel cA cc0 wne wa cB cc
    wcel cB cc0 wne wa wa cB cc wcel cA cc wcel cA cc0 wne cB cA cdiv co cc
    wcel cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cc wcel cB
    cc0 wne cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa simpr simpld cA
    cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cc wcel cA cc0 wne
    cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa simpl simpld cA cc wcel
    cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cc wcel cA cc0 wne cA cc
    wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa simpl simprd cB cA divcl
    syl3anc cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cc wcel
    cB cc0 wne wa cA cc wcel cA cc0 wne wa wa cB cA cdiv co cc0 wne cA cc
    wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cB cc wcel cB cc0 wne wa
    cA cc wcel cA cc0 wne wa cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne
    wa simpr cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa simpl jca cB
    cA divne0 syl logcld imcld cpi cr wcel cA cc wcel cA cc0 wne wa cB cc
    wcel cB cc0 wne wa wa pire a1i cB cA cdiv co clog cfv cim cfv cpi absle
    syl2anc mpbir2and cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa
    cc0 cr wcel cpi cr wcel cB cA cdiv co clog cfv cim cfv cabs cfv cc0 cpi
    cicc co wcel cB cA cdiv co clog cfv cim cfv cabs cfv cr wcel cc0 cB cA
    cdiv co clog cfv cim cfv cabs cfv cle wbr cB cA cdiv co clog cfv cim cfv
    cabs cfv cpi cle wbr w3a wb cc0 cr wcel cA cc wcel cA cc0 wne wa cB cc
    wcel cB cc0 wne wa wa 0re a1i cpi cr wcel cA cc wcel cA cc0 wne wa cB cc
    wcel cB cc0 wne wa wa pire a1i cc0 cpi cB cA cdiv co clog cfv cim cfv
    cabs cfv elicc2 syl2anc mpbir3and eqeltrd $.

  glawcos $p |- ( ( ( A e. CC /\ B e. CC /\ C e. CC ) /\ ( -. A = B /\ -. C = B ) ) -> ( ( abs ` ( C - A ) ) ^ 2 ) = ( ( ( ( abs ` ( A - B ) ) ^ 2 ) + ( ( abs ` ( B - C ) ) ^ 2 ) ) - ( 2 x. ( ( ( abs ` ( A - B ) ) x. ( abs ` ( B - C ) ) ) x. ( cos ` ( abs ` ( ( A - B ) ang ( C - B ) ) ) ) ) ) ) ) $=
    cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cC
    cA cmin co cabs cfv c2 cexp co cA cB cmin co cabs cfv c2 cexp co cC cB
    cmin co cabs cfv c2 cexp co caddc co c2 cA cB cmin co cabs cfv cC cB cmin
    co cabs cfv cmul co cA cB cmin co cC cB cmin co cang co ccos cfv cmul co
    cmul co cmin co cA cB cmin co cabs cfv c2 cexp co cB cC cmin co cabs cfv
    c2 cexp co caddc co c2 cA cB cmin co cabs cfv cB cC cmin co cabs cfv cmul
    co cA cB cmin co cC cB cmin co cang co cabs cfv ccos cfv cmul co cmul co
    cmin co cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn
    wa wa cC cc wcel cA cc wcel cB cc wcel w3a cC cB wne cA cB wne wa cC cA
    cmin co cabs cfv c2 cexp co cA cB cmin co cabs cfv c2 cexp co cC cB cmin
    co cabs cfv c2 cexp co caddc co c2 cA cB cmin co cabs cfv cC cB cmin co
    cabs cfv cmul co cA cB cmin co cC cB cmin co cang co ccos cfv cmul co
    cmul co cmin co wceq cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn
    cC cB wceq wn wa wa cC cc wcel cA cc wcel cB cc wcel cA cc wcel cB cc
    wcel cC cc wcel w3a cC cc wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel
    cB cc wcel cC cc wcel simp3 adantr cA cc wcel cB cc wcel cC cc wcel w3a
    cA cc wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel cB cc wcel cC cc
    wcel simp1 adantr cA cc wcel cB cc wcel cC cc wcel w3a cB cc wcel cA cB
    wceq wn cC cB wceq wn wa cA cc wcel cB cc wcel cC cc wcel simp2 adantr
    3jca cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa
    wa cC cB wne cA cB wne cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn
    cC cB wceq wn wa wa cC cB cA cB wceq wn cC cB wceq wn wa cC cB wceq wn cA
    cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn simpr
    adantl neqned cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB
    wceq wn wa wa cA cB cA cB wceq wn cC cB wceq wn wa cA cB wceq wn cA cc
    wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn simpl adantl
    neqned jca vx vy cC cA cB cang cA cB cmin co cC cB cmin co cang co cA cB
    cmin co cabs cfv cC cB cmin co cabs cfv cC cA cmin co cabs cfv vx vy
    df-ang cA cB cmin co cabs cfv eqid cC cB cmin co cabs cfv eqid cC cA cmin
    co cabs cfv eqid cA cB cmin co cC cB cmin co cang co eqid lawcos syl2anc
    cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cA
    cB cmin co cabs cfv c2 cexp co cC cB cmin co cabs cfv c2 cexp co caddc co
    cA cB cmin co cabs cfv c2 cexp co cB cC cmin co cabs cfv c2 cexp co caddc
    co c2 cA cB cmin co cabs cfv cC cB cmin co cabs cfv cmul co cA cB cmin co
    cC cB cmin co cang co ccos cfv cmul co cmul co c2 cA cB cmin co cabs cfv
    cB cC cmin co cabs cfv cmul co cA cB cmin co cC cB cmin co cang co cabs
    cfv ccos cfv cmul co cmul co cmin cA cc wcel cB cc wcel cC cc wcel w3a cA
    cB wceq wn cC cB wceq wn wa wa cC cB cmin co cabs cfv c2 cexp co cB cC
    cmin co cabs cfv c2 cexp co cA cB cmin co cabs cfv c2 cexp co caddc cA cc
    wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cC cB
    cmin co cabs cfv cB cC cmin co cabs cfv c2 cexp cA cc wcel cB cc wcel cC
    cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cC cc wcel cB cc wcel cC cB
    cmin co cabs cfv cB cC cmin co cabs cfv wceq cA cc wcel cB cc wcel cC cc
    wcel w3a cC cc wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel cB cc wcel
    cC cc wcel simp3 adantr cA cc wcel cB cc wcel cC cc wcel w3a cB cc wcel
    cA cB wceq wn cC cB wceq wn wa cA cc wcel cB cc wcel cC cc wcel simp2
    adantr cC cB abssub syl2anc oveq1d oveq2d cA cc wcel cB cc wcel cC cc
    wcel w3a cA cB wceq wn cC cB wceq wn wa wa cA cB cmin co cabs cfv cC cB
    cmin co cabs cfv cmul co cA cB cmin co cC cB cmin co cang co ccos cfv
    cmul co cA cB cmin co cabs cfv cB cC cmin co cabs cfv cmul co cA cB cmin
    co cC cB cmin co cang co cabs cfv ccos cfv cmul co c2 cmul cA cc wcel cB
    cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cA cB cmin co
    cabs cfv cC cB cmin co cabs cfv cmul co cA cB cmin co cabs cfv cB cC cmin
    co cabs cfv cmul co cA cB cmin co cC cB cmin co cang co ccos cfv cA cB
    cmin co cC cB cmin co cang co cabs cfv ccos cfv cmul cA cc wcel cB cc
    wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cC cB cmin co cabs
    cfv cB cC cmin co cabs cfv cA cB cmin co cabs cfv cmul cA cc wcel cB cc
    wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cC cc wcel cB cc
    wcel cC cB cmin co cabs cfv cB cC cmin co cabs cfv wceq cA cc wcel cB cc
    wcel cC cc wcel w3a cC cc wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel
    cB cc wcel cC cc wcel simp3 adantr cA cc wcel cB cc wcel cC cc wcel w3a
    cB cc wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel cB cc wcel cC cc
    wcel simp2 adantr cC cB abssub syl2anc oveq2d cA cc wcel cB cc wcel cC cc
    wcel w3a cA cB wceq wn cC cB wceq wn wa wa cA cB cmin co cC cB cmin co
    cang co cabs cfv ccos cfv cA cB cmin co cC cB cmin co cang co ccos cfv cA
    cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cA cB
    cmin co cC cB cmin co cang co cr wcel cA cB cmin co cC cB cmin co cang co
    cabs cfv ccos cfv cA cB cmin co cC cB cmin co cang co ccos cfv wceq cA cc
    wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cA cB
    cmin co cC cB cmin co cang co cC cB cmin co cA cB cmin co cdiv co clog
    cfv cim cfv cr cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB
    wceq wn wa wa cA cB cmin co cc wcel cA cB cmin co cc0 wne wa cC cB cmin
    co cc wcel cC cB cmin co cc0 wne wa wa cA cB cmin co cC cB cmin co cang
    co cC cB cmin co cA cB cmin co cdiv co clog cfv cim cfv wceq cA cc wcel
    cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cA cB cmin co
    cc wcel cA cB cmin co cc0 wne wa cC cB cmin co cc wcel cC cB cmin co cc0
    wne wa cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn
    wa wa cA cB cmin co cc wcel cA cB cmin co cc0 wne cA cc wcel cB cc wcel
    cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cA cB cA cc wcel cB cc
    wcel cC cc wcel w3a cA cc wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel
    cB cc wcel cC cc wcel simp1 adantr cA cc wcel cB cc wcel cC cc wcel w3a
    cB cc wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel cB cc wcel cC cc
    wcel simp2 adantr subcld cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq
    wn cC cB wceq wn wa wa cA cB cmin co cc0 wne cA cB wne cA cc wcel cB cc
    wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cA cB cA cB wceq wn
    cC cB wceq wn wa cA cB wceq wn cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    wceq wn cC cB wceq wn simpl adantl neqned cA cc wcel cB cc wcel cC cc
    wcel w3a cA cB wceq wn cC cB wceq wn wa wa cA cB cmin co cc0 cA cB cA cc
    wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cA cB cA
    cc wcel cB cc wcel cC cc wcel w3a cA cc wcel cA cB wceq wn cC cB wceq wn
    wa cA cc wcel cB cc wcel cC cc wcel simp1 adantr cA cc wcel cB cc wcel cC
    cc wcel w3a cB cc wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel cB cc
    wcel cC cc wcel simp2 adantr subeq0ad necon3bid mpbird jca cA cc wcel cB
    cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cC cB cmin co cc
    wcel cC cB cmin co cc0 wne cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    wceq wn cC cB wceq wn wa wa cC cB cA cc wcel cB cc wcel cC cc wcel w3a cC
    cc wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel cB cc wcel cC cc wcel
    simp3 adantr cA cc wcel cB cc wcel cC cc wcel w3a cB cc wcel cA cB wceq
    wn cC cB wceq wn wa cA cc wcel cB cc wcel cC cc wcel simp2 adantr subcld
    cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cC
    cB cmin co cc0 wne cC cB wne cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    wceq wn cC cB wceq wn wa wa cC cB cA cB wceq wn cC cB wceq wn wa cC cB
    wceq wn cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn
    simpr adantl neqned cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC
    cB wceq wn wa wa cC cB cmin co cc0 cC cB cA cc wcel cB cc wcel cC cc wcel
    w3a cA cB wceq wn cC cB wceq wn wa wa cC cB cA cc wcel cB cc wcel cC cc
    wcel w3a cC cc wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel cB cc wcel
    cC cc wcel simp3 adantr cA cc wcel cB cc wcel cC cc wcel w3a cB cc wcel
    cA cB wceq wn cC cB wceq wn wa cA cc wcel cB cc wcel cC cc wcel simp2
    adantr subeq0ad necon3bid mpbird jca jca cA cB cmin co cC cB cmin co
    gangval syl cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq
    wn wa wa cC cB cmin co cA cB cmin co cdiv co clog cfv cA cc wcel cB cc
    wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cC cB cmin co cA cB
    cmin co cdiv co cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB
    wceq wn wa wa cC cB cmin co cA cB cmin co cA cc wcel cB cc wcel cC cc
    wcel w3a cA cB wceq wn cC cB wceq wn wa wa cC cB cA cc wcel cB cc wcel cC
    cc wcel w3a cC cc wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel cB cc
    wcel cC cc wcel simp3 adantr cA cc wcel cB cc wcel cC cc wcel w3a cB cc
    wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel cB cc wcel cC cc wcel
    simp2 adantr subcld cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC
    cB wceq wn wa wa cA cB cA cc wcel cB cc wcel cC cc wcel w3a cA cc wcel cA
    cB wceq wn cC cB wceq wn wa cA cc wcel cB cc wcel cC cc wcel simp1 adantr
    cA cc wcel cB cc wcel cC cc wcel w3a cB cc wcel cA cB wceq wn cC cB wceq
    wn wa cA cc wcel cB cc wcel cC cc wcel simp2 adantr subcld cA cc wcel cB
    cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cA cB cmin co
    cc0 wne cA cB wne cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC
    cB wceq wn wa wa cA cB cA cB wceq wn cC cB wceq wn wa cA cB wceq wn cA cc
    wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn simpl adantl
    neqned cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn
    wa wa cA cB cmin co cc0 cA cB cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    wceq wn cC cB wceq wn wa wa cA cB cA cc wcel cB cc wcel cC cc wcel w3a cA
    cc wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel cB cc wcel cC cc wcel
    simp1 adantr cA cc wcel cB cc wcel cC cc wcel w3a cB cc wcel cA cB wceq
    wn cC cB wceq wn wa cA cc wcel cB cc wcel cC cc wcel simp2 adantr
    subeq0ad necon3bid mpbird divcld cA cc wcel cB cc wcel cC cc wcel w3a cA
    cB wceq wn cC cB wceq wn wa wa cC cB cmin co cA cB cmin co cA cc wcel cB
    cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cC cB cA cc wcel
    cB cc wcel cC cc wcel w3a cC cc wcel cA cB wceq wn cC cB wceq wn wa cA cc
    wcel cB cc wcel cC cc wcel simp3 adantr cA cc wcel cB cc wcel cC cc wcel
    w3a cB cc wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel cB cc wcel cC cc
    wcel simp2 adantr subcld cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq
    wn cC cB wceq wn wa wa cA cB cA cc wcel cB cc wcel cC cc wcel w3a cA cc
    wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel cB cc wcel cC cc wcel
    simp1 adantr cA cc wcel cB cc wcel cC cc wcel w3a cB cc wcel cA cB wceq
    wn cC cB wceq wn wa cA cc wcel cB cc wcel cC cc wcel simp2 adantr subcld
    cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cC
    cB cmin co cc0 wne cC cB wne cA cc wcel cB cc wcel cC cc wcel w3a cA cB
    wceq wn cC cB wceq wn wa wa cC cB cA cB wceq wn cC cB wceq wn wa cC cB
    wceq wn cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn
    simpr adantl neqned cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC
    cB wceq wn wa wa cC cB cmin co cc0 cC cB cA cc wcel cB cc wcel cC cc wcel
    w3a cA cB wceq wn cC cB wceq wn wa wa cC cB cA cc wcel cB cc wcel cC cc
    wcel w3a cC cc wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel cB cc wcel
    cC cc wcel simp3 adantr cA cc wcel cB cc wcel cC cc wcel w3a cB cc wcel
    cA cB wceq wn cC cB wceq wn wa cA cc wcel cB cc wcel cC cc wcel simp2
    adantr subeq0ad necon3bid mpbird cA cc wcel cB cc wcel cC cc wcel w3a cA
    cB wceq wn cC cB wceq wn wa wa cA cB cmin co cc0 wne cA cB wne cA cc wcel
    cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cA cB cA cB
    wceq wn cC cB wceq wn wa cA cB wceq wn cA cc wcel cB cc wcel cC cc wcel
    w3a cA cB wceq wn cC cB wceq wn simpl adantl neqned cA cc wcel cB cc wcel
    cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cA cB cmin co cc0 cA cB
    cA cc wcel cB cc wcel cC cc wcel w3a cA cB wceq wn cC cB wceq wn wa wa cA
    cB cA cc wcel cB cc wcel cC cc wcel w3a cA cc wcel cA cB wceq wn cC cB
    wceq wn wa cA cc wcel cB cc wcel cC cc wcel simp1 adantr cA cc wcel cB cc
    wcel cC cc wcel w3a cB cc wcel cA cB wceq wn cC cB wceq wn wa cA cc wcel
    cB cc wcel cC cc wcel simp2 adantr subeq0ad necon3bid mpbird divne0d
    logcld imcld eqeltrd cA cB cmin co cC cB cmin co cang co gcosabs syl
    eqcomd oveq12d oveq2d oveq12d eqtrd $.

  gcoscan $p |- ( ( ( X e. CC /\ Y e. CC /\ Z e. CC ) /\ ( K e. CC /\ K =/= 0 ) ) -> ( ( Z - ( 2 x. ( K x. X ) ) ) = ( Z - ( 2 x. ( K x. Y ) ) ) -> X = Y ) ) $=
    cX cc wcel cY cc wcel cZ cc wcel w3a cK cc wcel cK cc0 wne wa wa cZ c2 cK
    cX cmul co cmul co cmin co cZ c2 cK cY cmul co cmul co cmin co wceq cK cX
    cmul co cK cY cmul co wceq cX cY wceq cX cc wcel cY cc wcel cZ cc wcel
    w3a cK cc wcel cK cc0 wne wa wa cZ c2 cK cX cmul co cmul co cmin co cZ c2
    cK cY cmul co cmul co cmin co wceq c2 cK cX cmul co cmul co c2 cK cY cmul
    co cmul co wceq cK cX cmul co cK cY cmul co wceq cX cc wcel cY cc wcel cZ
    cc wcel w3a cK cc wcel cK cc0 wne wa wa cZ c2 cK cX cmul co cmul co cmin
    co cZ c2 cK cY cmul co cmul co cmin co wceq c2 cK cX cmul co cmul co c2
    cK cY cmul co cmul co wceq cX cc wcel cY cc wcel cZ cc wcel w3a cK cc
    wcel cK cc0 wne wa wa cZ cc wcel c2 cK cX cmul co cmul co cc wcel c2 cK
    cY cmul co cmul co cc wcel cZ c2 cK cX cmul co cmul co cmin co cZ c2 cK
    cY cmul co cmul co cmin co wceq c2 cK cX cmul co cmul co c2 cK cY cmul co
    cmul co wceq wb cX cc wcel cY cc wcel cZ cc wcel w3a cK cc wcel cK cc0
    wne wa wa cX cc wcel cY cc wcel cZ cc wcel w3a cZ cc wcel cX cc wcel cY
    cc wcel cZ cc wcel w3a cK cc wcel cK cc0 wne wa simpl cX cc wcel cY cc
    wcel cZ cc wcel simp3 syl cX cc wcel cY cc wcel cZ cc wcel w3a cK cc wcel
    cK cc0 wne wa wa c2 cK cX cmul co c2 cc wcel cX cc wcel cY cc wcel cZ cc
    wcel w3a cK cc wcel cK cc0 wne wa wa 2cn a1i cX cc wcel cY cc wcel cZ cc
    wcel w3a cK cc wcel cK cc0 wne wa wa cK cX cX cc wcel cY cc wcel cZ cc
    wcel w3a cK cc wcel cK cc0 wne wa wa cK cc wcel cK cc0 wne cX cc wcel cY
    cc wcel cZ cc wcel w3a cK cc wcel cK cc0 wne wa simpr simpld cX cc wcel
    cY cc wcel cZ cc wcel w3a cK cc wcel cK cc0 wne wa wa cX cc wcel cY cc
    wcel cZ cc wcel w3a cX cc wcel cX cc wcel cY cc wcel cZ cc wcel w3a cK cc
    wcel cK cc0 wne wa simpl cX cc wcel cY cc wcel cZ cc wcel simp1 syl
    mulcld mulcld cX cc wcel cY cc wcel cZ cc wcel w3a cK cc wcel cK cc0 wne
    wa wa c2 cK cY cmul co c2 cc wcel cX cc wcel cY cc wcel cZ cc wcel w3a cK
    cc wcel cK cc0 wne wa wa 2cn a1i cX cc wcel cY cc wcel cZ cc wcel w3a cK
    cc wcel cK cc0 wne wa wa cK cY cX cc wcel cY cc wcel cZ cc wcel w3a cK cc
    wcel cK cc0 wne wa wa cK cc wcel cK cc0 wne cX cc wcel cY cc wcel cZ cc
    wcel w3a cK cc wcel cK cc0 wne wa simpr simpld cX cc wcel cY cc wcel cZ
    cc wcel w3a cK cc wcel cK cc0 wne wa wa cX cc wcel cY cc wcel cZ cc wcel
    w3a cY cc wcel cX cc wcel cY cc wcel cZ cc wcel w3a cK cc wcel cK cc0 wne
    wa simpl cX cc wcel cY cc wcel cZ cc wcel simp2 syl mulcld mulcld cZ c2
    cK cX cmul co cmul co c2 cK cY cmul co cmul co subcan syl3anc biimpd cX
    cc wcel cY cc wcel cZ cc wcel w3a cK cc wcel cK cc0 wne wa wa cK cX cmul
    co cc wcel cK cY cmul co cc wcel c2 cc wcel c2 cc0 wne wa c2 cK cX cmul
    co cmul co c2 cK cY cmul co cmul co wceq cK cX cmul co cK cY cmul co wceq
    wb cX cc wcel cY cc wcel cZ cc wcel w3a cK cc wcel cK cc0 wne wa wa cK cX
    cX cc wcel cY cc wcel cZ cc wcel w3a cK cc wcel cK cc0 wne wa wa cK cc
    wcel cK cc0 wne cX cc wcel cY cc wcel cZ cc wcel w3a cK cc wcel cK cc0
    wne wa simpr simpld cX cc wcel cY cc wcel cZ cc wcel w3a cK cc wcel cK
    cc0 wne wa wa cX cc wcel cY cc wcel cZ cc wcel w3a cX cc wcel cX cc wcel
    cY cc wcel cZ cc wcel w3a cK cc wcel cK cc0 wne wa simpl cX cc wcel cY cc
    wcel cZ cc wcel simp1 syl mulcld cX cc wcel cY cc wcel cZ cc wcel w3a cK
    cc wcel cK cc0 wne wa wa cK cY cX cc wcel cY cc wcel cZ cc wcel w3a cK cc
    wcel cK cc0 wne wa wa cK cc wcel cK cc0 wne cX cc wcel cY cc wcel cZ cc
    wcel w3a cK cc wcel cK cc0 wne wa simpr simpld cX cc wcel cY cc wcel cZ
    cc wcel w3a cK cc wcel cK cc0 wne wa wa cX cc wcel cY cc wcel cZ cc wcel
    w3a cY cc wcel cX cc wcel cY cc wcel cZ cc wcel w3a cK cc wcel cK cc0 wne
    wa simpl cX cc wcel cY cc wcel cZ cc wcel simp2 syl mulcld cX cc wcel cY
    cc wcel cZ cc wcel w3a cK cc wcel cK cc0 wne wa wa c2 cc wcel c2 cc0 wne
    c2 cc wcel cX cc wcel cY cc wcel cZ cc wcel w3a cK cc wcel cK cc0 wne wa
    wa 2cn a1i c2 cc0 wne cX cc wcel cY cc wcel cZ cc wcel w3a cK cc wcel cK
    cc0 wne wa wa 2ne0 a1i jca cK cX cmul co cK cY cmul co c2 mulcan syl3anc
    sylibd cX cc wcel cY cc wcel cZ cc wcel w3a cK cc wcel cK cc0 wne wa wa
    cX cc wcel cY cc wcel cK cc wcel cK cc0 wne wa cK cX cmul co cK cY cmul
    co wceq cX cY wceq wb cX cc wcel cY cc wcel cZ cc wcel w3a cK cc wcel cK
    cc0 wne wa wa cX cc wcel cY cc wcel cZ cc wcel w3a cX cc wcel cX cc wcel
    cY cc wcel cZ cc wcel w3a cK cc wcel cK cc0 wne wa simpl cX cc wcel cY cc
    wcel cZ cc wcel simp1 syl cX cc wcel cY cc wcel cZ cc wcel w3a cK cc wcel
    cK cc0 wne wa wa cX cc wcel cY cc wcel cZ cc wcel w3a cY cc wcel cX cc
    wcel cY cc wcel cZ cc wcel w3a cK cc wcel cK cc0 wne wa simpl cX cc wcel
    cY cc wcel cZ cc wcel simp2 syl cX cc wcel cY cc wcel cZ cc wcel w3a cK
    cc wcel cK cc0 wne wa simpr cX cY cK mulcan syl3anc sylibd $.

  gangeq $p |- ( ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) /\ ( ( C e. CC /\ C =/= 0 ) /\ ( D e. CC /\ D =/= 0 ) ) ) -> ( ( cos ` ( abs ` ( A ang B ) ) ) = ( cos ` ( abs ` ( C ang D ) ) ) -> ( abs ` ( A ang B ) ) = ( abs ` ( C ang D ) ) ) ) $=
    cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cC cc wcel cC cc0
    wne wa cD cc wcel cD cc0 wne wa wa wa cA cB cang co cabs cfv cC cD cang
    co cabs cfv wceq cA cB cang co cabs cfv ccos cfv cC cD cang co cabs cfv
    ccos cfv wceq cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cC cc
    wcel cC cc0 wne wa cD cc wcel cD cc0 wne wa wa wa cA cB cang co cabs cfv
    cc0 cpi cicc co wcel cC cD cang co cabs cfv cc0 cpi cicc co wcel cA cB
    cang co cabs cfv cC cD cang co cabs cfv wceq cA cB cang co cabs cfv ccos
    cfv cC cD cang co cabs cfv ccos cfv wceq wb cA cc wcel cA cc0 wne wa cB
    cc wcel cB cc0 wne wa wa cC cc wcel cC cc0 wne wa cD cc wcel cD cc0 wne
    wa wa wa cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cA cB cang
    co cabs cfv cc0 cpi cicc co wcel cA cc wcel cA cc0 wne wa cB cc wcel cB
    cc0 wne wa wa cC cc wcel cC cc0 wne wa cD cc wcel cD cc0 wne wa wa simpl
    cA cB gangrange syl cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa
    cC cc wcel cC cc0 wne wa cD cc wcel cD cc0 wne wa wa wa cC cc wcel cC cc0
    wne wa cD cc wcel cD cc0 wne wa wa cC cD cang co cabs cfv cc0 cpi cicc co
    wcel cA cc wcel cA cc0 wne wa cB cc wcel cB cc0 wne wa wa cC cc wcel cC
    cc0 wne wa cD cc wcel cD cc0 wne wa wa simpr cC cD gangrange syl cA cB
    cang co cabs cfv cC cD cang co cabs cfv cos11 syl2anc biimprd $.

