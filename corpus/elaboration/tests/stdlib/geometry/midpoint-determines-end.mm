$( tests/stdlib/geometry/midpoint-determines-end, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.midpoint-determines-end $p |- ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. CC ) /\ ( ( A =/= D /\ ( ( B - D ) / ( A - D ) ) e. RR /\ ( ( B - D ) / ( A - D ) ) < 0 ) /\ ( abs ` ( A - D ) ) = ( abs ` ( D - B ) ) ) ) /\ ( ( A =/= D /\ ( ( C - D ) / ( A - D ) ) e. RR /\ ( ( C - D ) / ( A - D ) ) < 0 ) /\ ( abs ` ( A - D ) ) = ( abs ` ( D - C ) ) ) ) -> B = C ) $=
    ( cc wcel wa wne cmin co cdiv cr cc0 clt wbr w3a cabs cfv wceq simpl simpr syl jca wi id gmidend mpd ) AEFZBEFZGZCEFZGZDEFZGZADHZBDIJZADIJZKJZLFZURMNOZPZUQQRZDBIJZQRZSZGZGZUOCDIJZUQKJZLFZVIMNOZPZVBDCIJZQRZSZGZGZVFVPGZBCSZVQVFVPVQVGVFVGVPTZUNVFUAUBVGVPUAUCVQUJUKUMGZGVRVSUDVQUJWAVQUHUIVQVGUHVTVGUNUHUNVFTZUNULUHULUMTZULUJUHUJUKTZUJUHUHUHUITUHUEUBUBUBUBUBVQVGUIVTVGUNUIWBUNULUIWCULUJUIWDUHUIUAUBUBUBUBUCVQUKUMVQVGUKVTVGUNUKWBUNULUKWCUJUKUAUBUBUBVQVGUMVTVGUNUMWBULUMUAUBUBUCUCABCDUFUBUG $.
$}
