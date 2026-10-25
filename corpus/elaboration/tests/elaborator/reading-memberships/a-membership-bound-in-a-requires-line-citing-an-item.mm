$( tests/elaborator/reading-memberships/a-membership-bound-in-a-requires-line-citing-an-item, elaborated from tests/elaborator/reading-memberships.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.reading-memberships.a-membership-bound-in-a-requires-line-citing-an-item $p |- ( ( ( A e. RR /\ -. A = 0 ) /\ B e. NN ) -> 0 < ( ( A x. B ) ^ 2 ) ) $=
    ( cr wcel cc0 wceq wn wa cn cmul co wne c2 cexp clt wbr simpl id syl simpr nnre remulcld cc recn neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid jca nncn nnne0 mulne0 sqgt0 ) ACDZAEFZGZHZBIDZHZABJKZCDZVEELZHEVEMNKOPVDVFVGVDABVDVBUSVBVCQZVBUSUSUSVAQZUSRZSZSZVDVCBCDVBVCTZBUASUBVDVEEFZGZVGVDVGVOVDAUCDZAELZHZBUCDZBELZHZHVGVDVRWAVDVPVQVDUSVPVLAUDSVDEAFZGZVQVDAEVDVBVAVHUSVATSUEVDVQWCVDVQVAWCVQVAUFVDAEUGUHVDUTWBVDWBUTWBUTUFVDEAUIUHUJUKULUJUMUNVDVSVTVDVCVSVMBUOSVDVCVTVMBUPSUNUNABUQSVGVOUFZVDVEEUGZUHZUMVDVGVOWFUJUMUNVEURS $.
$}
