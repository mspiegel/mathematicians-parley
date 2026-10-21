$( tests/stdlib/geometry/heron, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.heron $p |- ( ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ D e. RR ) /\ -. A = C ) /\ -. B = C ) /\ D = ( ( ( ( abs ` ( B - C ) ) + ( abs ` ( A - C ) ) ) + ( abs ` ( A - B ) ) ) / 2 ) ) -> ( ( ( 1 / 2 ) x. ( ( abs ` ( B - C ) ) x. ( abs ` ( A - C ) ) ) ) x. ( abs ` ( sin ` ( ( B - C ) ang ( A - C ) ) ) ) ) = ( sqrt ` ( ( D x. ( D - ( abs ` ( B - C ) ) ) ) x. ( ( D - ( abs ` ( A - C ) ) ) x. ( D - ( abs ` ( A - B ) ) ) ) ) ) ) $=
    ( cc wcel wa cr wceq wn cmin co cabs cfv caddc c2 cdiv c1 cmul cang csin csqrt simpr w3a wne wi simpl id syl 3jca neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid jca gheron mpd ) AEFZBEFZGZCEFZGZDHFZGZACIZJZGZBCIZJZGZDBCKLZMNZACKLZMNZOLZABKLZMNZOLZPQLZIZGZWERPQLZVQVSSLZSLZVPVRTLZUANZMNZSLZDDVQKLZSLZDVSKLZDWBKLZSLZSLZUBNZIZVOWEUCWFVCVDVFUDZACUEZBCUEZGZGWEXAUFWFXBXEWFVCVDVFWFVOVCVOWEUGZVOVLVCVLVNUGZVLVIVCVIVKUGZVIVGVCVGVHUGZVGVEVCVEVFUGZVEVCVCVCVDUGVCUHUIUIUIUIUIUIWFVOVDXFVOVLVDXGVLVIVDXHVIVGVDXIVGVEVDXJVCVDUCUIUIUIUIUIWFVOVFXFVOVLVFXGVLVIVFXHVIVGVFXIVEVFUCUIUIUIUIUJWFXCXDWFCAIZJZXCWFACWFVOVKXFVOVLVKXGVIVKUCUIUIUKWFXCXLWFXCVKXLXCVKULWFACUMUNWFVJXKWFXKVJXKVJULWFCAUOUNUPUQURUPUSWFCBIZJZXDWFBCWFVOVNXFVLVNUCUIUKWFXDXNWFXDVNXNXDVNULWFBCUMUNWFVMXMWFXMVMXMVMULWFCBUOUNUPUQURUPUSUTUTABCDVAUIVB $.
$}
