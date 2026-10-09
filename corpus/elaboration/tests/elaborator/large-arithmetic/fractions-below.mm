$( tests/elaborator/large-arithmetic/fractions-below, elaborated from tests/elaborator/large-arithmetic.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.large-arithmetic.fractions-below $p |- ( 2 / 3 ) < ( 5 / 7 ) $=
    ( c2 c3 cdiv co c5 c7 clt wbr wtru cmul c1 c4 cdc 1nn0 4nn0 5nn 4lt5 declt 2cn 7cn mulcomi 7t2e14 eqtri 5t3e15 breq12i mpbir cr wcel cc0 wa wb 2re 7re 7pos pm3.2i 5re 3re 3pos lt2mul2div ax-mp mpbi eqid oveq12i a1i mptru ) ABCDZEFCDZGHZVHIVHVHAFJDZEBJDZGHZVHVKKLMZKEMZGHKLENOPQRVIVLVJVMGVIFAJDVLAFSTUAUBUCUDUEUFAUGUHZFUGUHZUIFGHZUJZUJZEUGUHZBUGUHZUIBGHZUJZUJZUJVKVHUKVRWCVNVQULVOVPUMUNUOUOVSWBUPVTWAUQURUOUOUOAFEBUSUTVAVFVFVGVGGAABBCAVBBVBVCEEFFCEVBFVBVCUEUFVDVE $.
$}
