$( tests/notations/negatives/minus-times-minus, elaborated from tests/notations/negatives.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.notations.negatives.minus-times-minus $p |- ( -u 1 x. -u 1 ) = 1 $=
    ( c1 cneg cmul co wceq wtru cc wcel ax-1cn mulridi a1i eqcomd mulcld eqeltrd mulm1 syl oveq2d eqtrd negcld mulrid oveq1d wa jca mul4 mulneg1 syl2anc negeqd oveq12d mul2neg eqtr4d mptru ) ABZULCDZAEFUMAACDZAFUMULACDZUOCDZUNFULUOULUOCFULUOUNCDZUOFULULUNCDZUQFULUOURFUOULFAGHZUOULEZFAUNGFUNAUNAEZFAIJZKZLZFAAUSFIKZVEMZNZAOZPZLZFAUNULCVDQZRZFULUOUNCFUOULFULGHZUTFAVESZULTZPZLZUAZRZFUQUQUOFVMUSUBZUSUSUBZUBZUQUQEZFVTWAFVMUSVNVEUCZFUSUSVEVEUCZUCZULAAAUDZPZFUOULUNACFUOUNBZULFUSUSUOWIEZVEVEAAUEZUFZFUNAVCUGZRZFUSVAVEATZPZUHZRZRZWSUHFUPUMUNCDZUNFVTVTUBUPWTEFVTVTWDWDUCULAULAUDPFUMAUNACFUMUNAFUSUSUMUNEVEVEAAUIUFVCRWPUHRRVDUJUK $.
$}
