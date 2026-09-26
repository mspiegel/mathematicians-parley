$( tests/stdlib/sets/remove-member, elaborated from tests/stdlib/sets.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  removeme $p |- ( ( ( A e. _V /\ B e. _V ) /\ C e. _V ) -> ( C e. ( A \ { B } ) <-> ( C e. A /\ -. C = B ) ) ) $=
    ( cvv wcel wa csn cdif wne wb wceq wn eldifsn a1i df-ne anbi2d bibi2d mpbid ) ADEZBDEZFZCDEZFZCABGZHZEZCAEZCBIZFZJZUFUGCBKZLZFZJUJUCCABMNUCUIUMUFUCUHULUGUHULJUCCBONPQR $.
$}
