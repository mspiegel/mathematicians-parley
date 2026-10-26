$( tests/stdlib/trigonometry/arctan-values, elaborated from tests/stdlib/trigonometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.trigonometry.arctan-values $p |- ( ( arctan ` 0 ) = 0 /\ ( arctan ` 1 ) = ( _pi / 4 ) ) $=
    ( cc0 catan cfv wceq c1 cpi c4 cdiv co wa wtru atan0 a1i atan1 jca mptru ) ABCZADZEBCZFGHIZDZJKRUARKLMUAKNMOP $.
$}
