$( tests/elaborator/real-arithmetic-trigonometry/a-sine-said-once, elaborated from tests/elaborator/real-arithmetic-trigonometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.real-arithmetic-trigonometry.a-sine-said-once $p |- ( A e. RR -> ( A x. ( sin ` ( _pi / 6 ) ) ) = ( ( sin ` ( _pi / 6 ) ) x. A ) ) $=
    ( cr wcel cpi c6 cdiv co csin cfv cmul c1 cexp cc wceq id recn syl exp1 eqcomd cn0 1nn0 a1i expcld mullid eqtrd pire 6re cc0 wne 6ne0 redivcld resincld recnd oveq12d wa ax-1cn jca mul4 mulridi eqidd mulcom syl2anc eqtr4d ) ABCZADEFGZHIZJGZKAKLGZVFKLGZJGZJGZVFAJGZVDVGKVHJGZKVIJGZJGZVKVDAVMVFVNJVDAVHVMVDVHAVDAMCZVHANZVDVDVPVDOZAPZQZARZQZSZVDVMVHVDVHMCZVMVHNZVDAKVTKTCZVDUAUBZUCZVHUDZQZSZUEZVDVFVIVNVDVIVFVDVFMCZVIVFNZVDVFVDVEVDDEDBCZVDUFUBZEBCZVDUGUBZEUHUIZVDUJUBZUKZULZUMZVFRZQZSZVDVNVIVDVIMCZVNVINZVDVFKXCWGUCZVIUDZQZSZUEZUNVDVOKKJGZVJJGZVKVDKMCZWDUOZXPXGUOZUOVOXONVDXQXRVDXPWDXPVDUPUBZWHUQZVDXPXGXSXIUQZUQKVHKVIURQVDXNKVJVJJXNKNZVDKUPUSZUBZVDVJUTUNUEUEVDVLVNVMJGZVKVDVFVNAVMJXMWLUNVDYEXNVIVHJGZJGZVKVDXRXQUOYEYGNVDXRXQYAXTUQKVIKVHURQVDXNKYFVJJYDVDXGWDYFVJNXIWHVIVHVAVBUNUEUEVC $.
$}
