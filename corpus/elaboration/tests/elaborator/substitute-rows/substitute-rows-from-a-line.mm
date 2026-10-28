$( tests/elaborator/substitute-rows/substitute-rows-from-a-line, elaborated from tests/elaborator/substitute-rows.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.substitute-rows.substitute-rows-from-a-line $p |- ( ( ( ( A e. RR /\ B e. RR ) /\ A = 3 ) /\ ( ( A x. A ) + A ) < B ) -> ; 1 2 < B ) $=
    ( cr wcel wa c3 wceq cmul co caddc clt wbr c1 c2 cdc simpr simpl syl oveq12d breq1d mpbid c9 eqid oveq12i 3t3e9 eqtri 9p3e12 eqtr4i a1i ) ACDZBCDZEZAFGZEZAAHIZAJIZBKLZEZFFHIZFJIZBKLZMNOZBKLURUQVAUNUQPURUPUTBKURUOUSAFJURAFAFHURUNUMUNUQQZULUMPZRZVESVESTUAURUTVBBKUTVBGURUTVBVBUTUBFJIVBUSUBFFJUSUSUBFFFFHFUCZVFUDUEUFVFUDUGUFVBUCUHUITUA $.
$}
