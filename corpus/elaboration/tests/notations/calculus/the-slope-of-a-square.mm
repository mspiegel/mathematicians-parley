$( tests/notations/calculus/the-slope-of-a-square, elaborated from tests/notations/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d k m x $.
  $d A k m x $.
  tests.notations.calculus.the-slope-of-a-square $p |- ( ( A : RR --> RR /\ A. x e. RR ( A ` x ) = ( x ^ 2 ) ) -> A. x e. ( 0 (,) 1 ) ( ( RR _D A ) ` x ) = ( 2 x. x ) ) $=
    ( cr wf cv cfv c2 cexp co wceq wral wa vm cdv cmul cc0 c1 cioo wss ssid a1i cicc ioossicc wcel 0re 1re jca iccssre syl sstr crn ctg iooretop simpl id simpr wb vk fveq2d oveq1d eqeq12d cbvralvw bitri mpbid gdvsqv oveq2d ) CCBDZAEZBFZVHGHIZJZACKZLZMEZCBNIZFZGVNOIZJZMPQRIZKZVHVOFZGVHOIZJZAVSKZVMMCVSBCCSVMCTUAVMVSPQUBIZSZWECSZLVSCSVMWFWGWFVMPQUCUAVMPCUDZQCUDZLWGVMWHWIWHVMUEUAWIVMUFUAUGPQUHUIUGVSWECUJUIVSRUKULFUDVMPQUMUAVMVGVGVGVLUNVGUOUIVMVLVNBFZVNGHIZJZMCKZVGVLUPVLWMUQVMVLUREZBFZWNGHIZJZURCKWMVKWQAURCVHWNJZVIWOVJWPWRVHWNBWRUOZUSWRVHWNGHWSUTVAVBWQWLURMCWNVNJZWOWJWPWKWTWNVNBWTUOZUSWTWNVNGHXAUTVAVBVCUAVDVEVTWDUQVMVTWNVOFZGWNOIZJZURVSKWDVRXDMURVSVNWNJZVPXBVQXCXEVNWNVOXEUOZUSXEVNWNGOXFVFVAVBXDWCURAVSWNVHJZXBWAXCWBXGWNVHVOXGUOZUSXGWNVHGOXHVFVAVBVCUAVD $.
$}
