$( tests/elaborator/large-arithmetic/sides-equal, elaborated from tests/elaborator/large-arithmetic.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.large-arithmetic.sides-equal $p |- ( ( 3 x. 4 ) + ( 2 ^ 3 ) ) <_ ; 2 0 $=
    ( c3 c4 cmul co c2 cexp caddc cc0 cdc cle wbr wtru cr wcel 2nn0 0nn0 deccl nn0rei a1i leid syl c1 c8 eqid oveq12i 3cn 4cn mulcomi 4t3e12 eqtri 2p1e3 1nn0 1p1e2 numexp1 oveq1i 2t2e4 numexpp1 4t2e8 8nn0 dec0h ax-1cn addridi 2cn 8cn addcomi 8p2e10 decaddc breq12i sylibr mptru ) ABCDZEAFDZGDZEHIZJKZLVNVNJKZVOLVNMNZVPVQLVNEHOPQRSVNTUAVMVNVNVNJVMUBEIZUCGDVNVKVRVLUCGVKVKVRAABBCAUDZBUDUEVKBACDVRABUFUGUHUIUJUJVLVLUCEEAAFEUDVSUEEUCEAOOUKEEFDZECDBECDUCVTBECEBUBEOULUMEUBFDZECDEECDBWAEECEOUNUOUPUJUQUOURUJUQUJUEUBEHUCEHVRUCULOPUSVRUDUCUSUTUBHGDZUBGDUBUBGDEWBUBUBGUBVAVBUOUMUJPEUCGDUCEGDUBHIEUCVCVDVEVFUJVGUJVNUDVHVIVJ $.
$}
