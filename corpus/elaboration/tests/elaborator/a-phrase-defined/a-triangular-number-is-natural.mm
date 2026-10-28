$( tests/elaborator/a-phrase-defined/a-triangular-number-is-natural, elaborated from tests/elaborator/a-phrase-defined.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A k $.
  tests.elaborator.a-phrase-defined.a-triangular-number-is-natural $p |- ( ( A e. RR /\ ( A e. NN /\ E. k e. NN A = ( ( k x. ( k + 1 ) ) / 2 ) ) ) -> A e. NN ) $=
    ( cr wcel cn cv c1 caddc co cmul c2 cdiv wceq wrex wa simpr wb biid a1i mpbid simpld ) ACDZAEDZABFZUDGHIZJIZKLIZMZBENZOZOZUCUIUKUJUJUBUJPUJUJQUKUJRSTUA $.
$}
