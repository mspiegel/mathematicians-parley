$( tests/docs/syntax/even-square, elaborated from tests/docs/syntax.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/wiedijk/sqrt2-irrational/odd-square.mm $]

${
  tests.docs.syntax.even-square $p |- ( ( A e. ZZ /\ 2 || ( A ^ 2 ) ) -> 2 || A ) $=
    ( cz wcel c2 cexp co cdvds wbr wa wn wo exmid a1i wi simpl id syl simpr jca proofs.wiedijk.sqrt2-irrational.odd-square notnot pm2.21dd ex pm2.01d orel2 mpd ) ABCZDADEFZGHZIZDAGHZUKJZKZUKUMUJUKLMUJULJZUMUKNUJULUJULUNUJULIZUIJZUNUOUGULIUPUOUGULUOUJUGUJULOZUJUGUGUGUIOUGPQQUJULRSATQUOUIUPJUOUJUIUQUGUIRQUIUAQUBUCUDULUKUEQUF $.
$}
