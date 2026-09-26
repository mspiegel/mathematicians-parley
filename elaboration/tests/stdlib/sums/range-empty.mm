$( tests/stdlib/sums/range-empty, elaborated from tests/stdlib/sums.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  rangeemp $p |- ( 1 ... 0 ) = (/) $=
    ( c1 cc0 cfz co c0 wceq wtru fz10 a1i mptru ) ABCDZEFZLGHIJ $.
$}
