$( tests/stdlib/numbers/nat0-member, elaborated from tests/stdlib/numbers.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  nat0memb $p |- ( A e. RR -> ( A e. NN0 <-> ( A e. NN \/ A = 0 ) ) ) $=
    ( cn0 wcel cn cc0 wceq wo wb cr elnn0 a1i ) ABCADCAEFGHAICAJK $.
$}
