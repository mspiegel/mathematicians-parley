$( tests/stdlib/sums/sum-empty-range, elaborated from tests/stdlib/sums.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.sums.sum-empty-range $p |- sum_ k e. ( 1 ... 0 ) ( ( 2 x. k ) - 1 ) = 0 $=
    ( c1 cc0 cfz co c2 cv cmul cmin csu wceq wtru cz wcel 1z a1i 0z clt wbr 0lt1 gfsum0 mptru ) BCDEFAGZHEZBIEZAJCKLUEABCBMNLOPCMNLQPCBRSLTPUAUB $.
$}
