$( tests/stdlib/numbers/quotient-real, elaborated from tests/stdlib/numbers.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  quotient $p |- ( ( ( A e. RR /\ B e. RR ) /\ -. B = 0 ) -> ( A / B ) e. RR ) $=
    ( cr wcel wa cc0 wceq wn wne w3a cdiv co simpl id syl simpr df-ne sylibr necom sylib 3jca redivcl ) ACDZBCDZEZBFGZHZEZUCUDBFIZJABKLCDUHUCUDUIUHUEUCUEUGMZUEUCUCUCUDMUCNOOUHUEUDUJUCUDPOUHFBIZUIUHUIUKUHUGUIUEUGPBFQRBFSTFBSTUAABUBO $.
$}
