$( tests/notations/numbers/sqrt-four, elaborated from tests/notations/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.notations.numbers.sqrt-four $p |- ( sqrt ` 4 ) = 2 $=
    ( c4 csqrt cfv c2 wceq wtru cexp co cc0 cle wbr wa cr wcel 4re a1i clt 4pos wi 0re ltle syl2anc mpd jca resqrtth syl sqrtge0 simpl eqid oveq12i c1 2nn0 1nn0 1p1e2 cmul numexp1 oveq1i 2t2e4 eqtri numexpp1 eqtr4i eqtrd wb resqrtcld simpr 2re 2pos sq11 mpbid mptru ) ABCZDEZFVKDGHZDDGHZEZVLFVMAVNFVMAEZIVKJKZLZVPFVPVQFAMNZIAJKZLZVPFVSVTVSFOPZFIAQKZVTWCFRPZFIMNZVSWCVTSZWEFTPZWBIAUAZUBZUCZUDZAUEZUFZFWAVQWKAUGZUFZUDZVPVQUHUFAVNEFAAVNAUIVNVNADDDDGDUIZWQUJDAUKDULUMUNDUKGHZDUOHDDUOHAWRDDUODULUPUQURUSUTUSVAPVBFVKMNZVQLZDMNZIDJKZLZLVOVLVCFWTXCFWSVQFAWBWJVDFVRVQWPVPVQVEUFUDFXAXBXAFVFPZFIDQKZXBXEFVGPFWEXAXEXBSWGXDIDUAUBUCUDUDVKDVHUFVIVJ $.
$}
