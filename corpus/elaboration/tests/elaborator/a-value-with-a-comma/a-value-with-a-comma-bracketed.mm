$( tests/elaborator/a-value-with-a-comma/a-value-with-a-comma-bracketed, elaborated from tests/elaborator/a-value-with-a-comma.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.a-value-with-a-comma.a-value-with-a-comma-bracketed $p |- ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. RR ) /\ ( ( A = B \/ ( ( C - A ) / ( B - A ) ) e. RR ) <-> D = 1 ) ) /\ -. D = 1 ) -> -. ( A = B \/ ( ( C - A ) / ( B - A ) ) e. RR ) ) $=
    ( cc wcel wa cr wceq cmin co cdiv wo c1 wb wn simpr simpl syl mtbird ) AEFZBEFZGZCEFZGZDHFZGZABIZCAJKZBAJKZLKZHFZMZDNIZOZGZUNPZGZUMUNUPUQQURUPUOUPUQRUGUOQST $.
$}
