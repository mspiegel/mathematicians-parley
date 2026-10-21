$( tests/elaborator/a-define-whose-body-the-reading-rewrites/a-define-whose-body-the-reading-rewrites, elaborated from tests/elaborator/a-define-whose-body-the-reading-rewrites.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d k m x $.
  $d A k m x $.
  $d B k m x $.
  tests.elaborator.a-define-whose-body-the-reading-rewrites.a-define-whose-body-the-reading-rewrites $p |- ( ( ( A e. RR /\ B e. RR ) /\ ( abs ` B ) = A ) -> B e. { x e. RR | ( abs ` x ) = A } ) $=
    ( cr wcel wa cabs cfv wceq vk cv vm crab wex cvv reex a1i rabexg syl elisset simpl simpr jca wb id fveq2d eqeq1d elrab mpbird eqcomd eleq2d mpbid cbvrabv eqtrd ex exlimdv mpd ) BDEZCDEZFZCGHZBIZFZJKZLKZGHZBIZLDMZIZJNZCAKZGHZBIZADMZEZVCVHOEZVJVCDOEZVPVQVCPQVGLDORSJVHOTSVCVIVOJVCVIVOVCVIFZCVDEZVOVRCVHEZVSVRVTUSVBFZVRUSVBVRVCUSVCVIUAZVCUTUSUTVBUAURUSUBSSVRVCVBWBUTVBUBSUCVTWAUDVRVGVBLCDVECIZVFVABWCVECGWCUEUFUGUHQUIVRVHVDCVRVDVHVCVIUBZUJUKULVRVDVNCVRVDVHVNWDVHVNIVRVGVMLADVEVKIZVFVLBWEVEVKGWEUEUFUGUMQUNUKULUOUPUQ $.
$}
