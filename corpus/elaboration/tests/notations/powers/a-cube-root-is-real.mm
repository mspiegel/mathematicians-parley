$( tests/notations/powers/a-cube-root-is-real, elaborated from tests/notations/powers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.notations.powers.a-cube-root-is-real $p |- ( A e. RR -> if ( 0 <_ A , ( A ^c ( 1 / 3 ) ) , -u ( -u A ^c ( 1 / 3 ) ) ) e. RR ) $=
    ( cr wcel cc0 cle wbr c1 c3 cdiv co ccxp cneg cif id gcbrtre syl ) ABCZQDAEFAGHIJZKJALRKJLMBCQNAOP $.
$}
