$( tests/stdlib/calculus/integral-is-real, elaborated from tests/stdlib/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d m s t $.
  $d A m s t $.
  $d B m s t $.
  $d C m s t $.
  $d D m s t $.
  tests.stdlib.calculus.integral-is-real $p |- ( ( ( ( ( ( A e. RR /\ B e. RR ) /\ A < B ) /\ C : ( A [,] B ) --> RR ) /\ ( C |` ( A [,] B ) ) e. ( ( A [,] B ) -cn-> RR ) ) /\ D e. ( A [,] B ) ) -> S_ [ A -> D ] ( C ` s ) _d s e. RR ) $=
    ( cr wcel wa clt wbr cicc co wf cres ccncf vt cv cfv cdit simpl id syl simpr gditgreres wb vm wceq fveq2d cbvditgv eleq1i bitri a1i mpbid ) AFGZBFGZHZABIJZHZABKLZFCMZHZCUSNZUSFOLZGZHZDUSGZHZPADPQZCRZSZFGZEADEQZCRZSZFGZVGPABDCVGVEUNVEVFTZVEVAUNVAVDTZVAURUNURUTTZURUPUNUPUQTZUPUNUNUNUOTUNUAUBUBUBUBUBVGVEUOVPVEVAUOVQVAURUOVRURUPUOVSUNUOUCUBUBUBUBVGVEUQVPVEVAUQVQVAURUQVRUPUQUCUBUBUBVGVEUTVPVEVAUTVQURUTUCUBUBVGVEVDVPVAVDUCUBVEVFUCUDVKVOUEVGVKUFADUFQZCRZSZFGVOVJWBFPUFADVIWAVHVTUGZVHVTCWCUAUHUIUJWBVNFUFEADWAVMVTVLUGZVTVLCWDUAUHUIUJUKULUM $.
$}
