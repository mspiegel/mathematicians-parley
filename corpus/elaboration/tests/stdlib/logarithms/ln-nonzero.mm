$( tests/stdlib/logarithms/ln-nonzero, elaborated from tests/stdlib/logarithms.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.logarithms.ln-nonzero $p |- ( ( ( A e. RR /\ 0 < A ) /\ -. A = 1 ) -> -. ( log ` A ) = 0 ) $=
    ( cr wcel cc0 clt wbr wa c1 wceq wn clog cfv wne crp simpl id syl simpr jca elrp sylibr neqcomd wb df-ne a1i eqcom notbid bitrd bicomd mpbid logne0 ) ABCZDAEFZGZAHIZJZGZAKLZDMZURDIZJZUQANCZAHMZGUSUQVBVCUQUNVBUQULUMUQUNULUNUPOZUNULULULUMOULPQQUQUNUMVDULUMRQSATUAUQHAIZJZVCUQAHUNUPRUBUQVCVFUQVCUPVFVCUPUCUQAHUDUEUQUOVEUOVEUCUQAHUFUEUGUHUIUJSAUKQUSVAUCUQURDUDUEUJ $.
$}
