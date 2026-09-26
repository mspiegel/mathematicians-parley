$( tests/stdlib/numbers/abs-power, elaborated from tests/stdlib/numbers.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  abspower $p |- ( ( A e. RR /\ B e. NN0 ) -> ( abs ` ( A ^ B ) ) = ( ( abs ` A ) ^ B ) ) $=
    ( cr wcel cn0 wa cc cexp co cabs cfv wceq simpl id syl recn simpr jca absexp ) ACDZBEDZFZAGDZUAFABHIJKAJKBHILUBUCUAUBTUCUBTTTUAMTNOAPOTUAQRABSO $.
$}
