$( tests/stdlib/numbers/le-cases, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.numbers.le-cases $p |- ( ( A e. RR /\ B e. RR ) -> ( A <_ B <-> ( A < B \/ A = B ) ) ) $=
    ( cr wcel wa cle wbr clt wceq wo wb simpl id syl simpr jca leloe ) ACDZBCDZEZTABFGABHGABIJKTRSTRRRSLRMNRSOPABQN $.
$}
