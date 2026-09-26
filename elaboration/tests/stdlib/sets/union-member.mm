$( tests/stdlib/sets/union-member, elaborated from tests/stdlib/sets.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  unionmem $p |- ( ( ( A e. _V /\ B e. _V ) /\ C e. _V ) -> ( C e. ( A u. B ) <-> ( C e. A \/ C e. B ) ) ) $=
    ( cun wcel wo wb cvv wa elun a1i ) CABDECAECBEFGAHEBHEICHEICABJK $.
$}
