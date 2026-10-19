$( tests/elaborator/real-arithmetic/a-root-below-a-numeral, elaborated from tests/elaborator/real-arithmetic.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.real-arithmetic.a-root-below-a-numeral $p |- ( sqrt ` 4 ) < 3 $=
    ( c4 csqrt cfv c3 clt wbr wtru c2 2lt3 a1i cexp co wceq eqid oveq12i c1 2nn0 1nn0 1p1e2 cmul numexp1 oveq1i 2t2e4 eqtri numexpp1 eqtr4i fveq2d cr wcel 2re cc0 cle 2pos wi 0re ltle syl2anc mpd sqrtsqd eqtrd eqidd breq12d mpbird mptru ) ABCZDEFZGVFHDEFZVGGIJGVEHDDEGVEHHGVEHHKLZBCHGAVHBAVHMGAAVHANVHVHAHHHHKHNZVIOHAPHQRSHPKLZHTLHHTLAVJHHTHQUAUBUCUDUEUDUFJUGGHHUHUIZGUJJZGUKHEFZUKHULFZVMGUMJGUKUHUIZVKVMVNUNVOGUOJVLUKHUPUQURUSUTGHVAUTGDVAVBVCVD $.
$}
