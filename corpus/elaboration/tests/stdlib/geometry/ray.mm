$( tests/stdlib/geometry/ray, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A u $.
  $d B u $.
  $d C u $.
  tests.stdlib.geometry.ray $p |- ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ -. B = C ) /\ ( ( ( A = B \/ A = C ) \/ ( B =/= A /\ ( ( C - A ) / ( B - A ) ) e. RR /\ ( ( C - A ) / ( B - A ) ) < 0 ) ) \/ ( B =/= C /\ ( ( A - C ) / ( B - C ) ) e. RR /\ ( ( A - C ) / ( B - C ) ) < 0 ) ) ) -> A e. { u e. CC | ( B = C \/ ( ( ( u - B ) / ( C - B ) ) e. RR /\ 0 <_ ( ( u - B ) / ( C - B ) ) ) ) } ) $=
    ( cc wcel wa wceq wn wo wne cmin co cdiv cr cc0 clt wbr w3a cv cle crab simpr wb simpl id syl jca neqcomd df-ne a1i eqcom bicomd notbid bitrd mpbid grayel mpbird ) BEFZCEFZGZDEFZGZCDHZIZGZBCHZBDHZJZCBKZDBLMZCBLMZNMZOFZVMPQRZSZJZCDKZBDLMZCDLMZNMZOFZWAPQRZSZJZGZBVDATZCLMZDCLMZNMZOFZPWJUARZGZJZAEUBZFZWEVFWEUCWFVCVRGWPWEUDWFVCVRWFVAVBWFUSUTWFVFUSVFWEUEZVFVCUSVCVEUEZVCVAUSVAVBUEZVAUSUSUSUTUEUSUFUGUGUGUGWFVFUTWQVFVCUTWRVCVAUTWSUSUTUCUGUGUGUHWFVFVBWQVFVCVBWRVAVBUCUGUGUHWFDCHZIZVRWFCDWFVFVEWQVCVEUCUGUIWFVRXAWFVRVEXAVRVEUDWFCDUJUKWFVDWTWFWTVDWTVDUDWFDCULUKUMUNUOUMUPUHACDBUQUGUR $.
$}
