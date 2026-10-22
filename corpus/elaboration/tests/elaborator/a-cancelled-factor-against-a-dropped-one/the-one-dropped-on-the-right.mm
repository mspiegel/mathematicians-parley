$( tests/elaborator/a-cancelled-factor-against-a-dropped-one/the-one-dropped-on-the-right, elaborated from tests/elaborator/a-cancelled-factor-against-a-dropped-one.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.a-cancelled-factor-against-a-dropped-one.the-one-dropped-on-the-right $p |- ( ( ( ( A e. RR /\ B e. RR ) /\ -. A = 0 ) /\ ( ( 2 x. B ) x. A ) = A ) -> ( 2 x. B ) = 1 ) $=
    ( cr wcel wa cc0 wceq wn c2 cmul co c1 cc 2cn a1i simpl simpr syl recn mulcld ax-1cn id wne neqcomd wb df-ne eqcom bicomd notbid bitrd mpbid eqcomd mullid eqeq1d mulcan2ad ) ACDZBCDZEZAFGZHZEZIBJKZAJKZAGZEZVBLAVEIBIMDVENOVEUQBMDVEVAUQVAVDPZVAURUQURUTPZUPUQQRRBSRTLMDVEUAOVEUPAMDZVEVAUPVFVAURUPVGURUPUPUPUQPZUPUBZRZRZRZASZRZVEFAGZHZAFUCZVEAFVEVAUTVFURUTQRUDVEVRVQVEVRUTVQVRUTUEVEAFUFOVEUSVPVEVPUSVPUSUEVEFAUGOUHUIUJUHUKVELAJKZVCVEAVCGVSVCGVEVCAVAVDQULVEAVSVCVEVSAVEVHVSAGVOAUMRULUNUKULUO $.
$}
