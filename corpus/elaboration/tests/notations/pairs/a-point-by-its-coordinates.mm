$( tests/notations/pairs/a-point-by-its-coordinates, elaborated from tests/notations/pairs.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.notations.pairs.a-point-by-its-coordinates $p |- ( ( ( ( A e. CC /\ B e. CC ) /\ A = ( 1 + ( _i x. 2 ) ) ) /\ ( abs ` ( A - B ) ) = 3 ) -> ( abs ` ( ( 1 + ( _i x. 2 ) ) - B ) ) = 3 ) $=
    ( cc wcel wa c1 ci c2 cmul co caddc wceq cmin cabs cfv c3 simpr simpl syl oveq1d fveq2d eqeq1d mpbid ) ACDZBCDZEZAFGHIJZKJZLZEZABMJZNOZPLZEZUMUHBMJZNOZPLUJUMQUNULUPPUNUKUONUNAUHBMUNUJUIUJUMRUFUIQSTUAUBUC $.
$}
