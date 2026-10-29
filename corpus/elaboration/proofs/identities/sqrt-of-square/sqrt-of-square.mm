$( proofs/identities/sqrt-of-square/sqrt-of-square, elaborated from proofs/identities/sqrt-of-square.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  proofs.identities.sqrt-of-square.sqrt-of-square $p |- ( A e. RR -> ( sqrt ` ( A ^ 2 ) ) = ( abs ` A ) ) $=
    ( cr wcel c2 cexp co csqrt cfv cabs wceq cc0 cle wbr wa id cn0 2nn0 a1i reexpcld sqge0 syl jca resqrtcl sqrtge0 resqrtth simpr absresq wb eqcom mpbid eqtrd simpl cc recn abscl absge0 sq11 ) ABCZADEFZGHZDEFZAIHZDEFZJZUTVBJZURVAUSVCURUTBCZKUTLMZNZVAUSJZNZVIURVHVIURVFVGURUSBCZKUSLMZNZVFURVKVLURADUROZDPCZURQRZSZURURVLVNATZUAZUBZUSUCZUAZURVMVGVTUSUDZUAZUBZURVMVIVTUSUEZUAZUBZVHVIUFUAURVCUSJZUSVCJZURURWIVNAUGUAWIWJUHURVCUSUIRUJUKURVHVBBCZKVBLMZNZNVDVEUHURVHWMURVJVHWHVHVIULUAURWKWLURAUMCZWKURURWNVNAUNZUAZAUOUAURWNWLWPAUPUAUBUBUTVBUQUAUJ $.
$}
