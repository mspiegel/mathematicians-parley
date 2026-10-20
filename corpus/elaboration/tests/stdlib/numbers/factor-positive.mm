$( tests/stdlib/numbers/factor-positive, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.factor-positive $p |- ( ( ( ( A e. RR /\ B e. RR ) /\ 0 <_ A ) /\ 0 < ( A x. B ) ) -> 0 < B ) $=
    ( cr wcel wa cc0 cle wbr cmul co clt simpl id syl simpr jca prodgt0 ) ACDZBCDZEZFAGHZEZFABIJZKHZEZTUAUDEZEFBKHUETUFUERSUEUBRUBUDLZUBTRTUALZTRRRSLRMNNNUEUBSUGUBTSUHRSONNPUEUAUDUEUBUAUGTUAONUBUDOPPABQN $.
$}
