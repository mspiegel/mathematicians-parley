$( tests/stdlib/calculus/continuous-of-a-difference, elaborated from tests/stdlib/calculus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d k m x $.
  $d A k m x $.
  $d B k m x $.
  $d C k m x $.
  tests.stdlib.calculus.continuous-of-a-difference $p |- ( ( ( ( ( ( A : RR --> RR /\ A e. ( RR -cn-> RR ) ) /\ B : RR --> RR ) /\ B e. ( RR -cn-> RR ) ) /\ C : RR --> RR ) /\ A. x e. RR ( C ` x ) = ( ( A ` x ) - ( B ` x ) ) ) -> C e. ( RR -cn-> RR ) ) $=
    ( cr wf ccncf co wcel wa cv cfv cmin wceq wral vm wss ssid a1i simpl simpr syl id wb vk fveq2d oveq12d eqeq12d cbvralvw bitri mpbid gcncfsub ) EEBFZBEEGHZIZJZEECFZJZCUNIZJZEEDFZJZAKZDLZVCBLZVCCLZMHZNZAEOZJZPEBCDEEQVJERSVJVBVAVBVITZUTVAUAUBVJVBUMVKVBUTUMUTVATZUTURUMURUSTZURUPUMUPUQTZUPUMUMUMUOTUMUCUBUBUBUBUBVJVBUQVKVBUTUQVLUTURUQVMUPUQUAUBUBUBVJVIPKZDLZVOBLZVOCLZMHZNZPEOZVBVIUAVIWAUDVJVIUEKZDLZWBBLZWBCLZMHZNZUEEOWAVHWGAUEEVCWBNZVDWCVGWFWHVCWBDWHUCZUFWHVEWDVFWEMWHVCWBBWIUFWHVCWBCWIUFUGUHUIWGVTUEPEWBVONZWCVPWFVSWJWBVODWJUCZUFWJWDVQWEVRMWJWBVOBWKUFWJWBVOCWKUFUGUHUIUJSUKVJVBUOVKVBUTUOVLUTURUOVMURUPUOVNUMUOUAUBUBUBUBVJVBUSVKVBUTUSVLURUSUAUBUBUL $.
$}
