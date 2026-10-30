$( tests/elaborator/an-identity-on-a-required-number/an-identity-on-a-required-number, elaborated from tests/elaborator/an-identity-on-a-required-number.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.an-identity-on-a-required-number.an-identity-on-a-required-number $p |- ( ( A : ZZ --> NN /\ B e. ZZ ) -> ( ( A ` B ) x. ( A ` B ) ) = ( 1 x. ( ( A ` B ) x. ( A ` B ) ) ) ) $=
    ( cz cn wf wcel wa cfv cmul co c1 c2 cexp cc wceq cr simpl id syl simpr ffvelcdm syl2anc nnre recn exp1 eqcomd cn0 1nn0 a1i expcld mullid eqtrd oveq12d ax-1cn jca mul4 mulridi eqidd caddc expadd syl3anc 1p1e2 oveq2d 2nn0 eqtr4d ) CDAEZBCFZGZBAHZVIIJZKVILMJZIJZKVJIJZVHVJKVIKMJZIJZVOIJZVLVHVIVOVIVOIVHVIVNVOVHVNVIVHVINFZVNVIOZVHVIPFZVQVHVIDFZVSVHVFVGVTVHVFVFVFVGQZVFRZSZVFVGTZCDBAUAZUBZVIUCZSZVIUDZSZVIUEZSZUFZVHVOVNVHVNNFZVOVNOZVHVIKWJKUGFZVHUHUIZUJZVNUKZSZUFZULZXBUMZVHVPKKIJZVNVNIJZIJZVLVHKNFZWNGZXHGZVPXFOZVHXHXHVHXGWNXGVHUNUIZWRUOZXLUOZKVNKVNUPZSZVHXDKXEVKIXDKOZVHKUNUQZUIZVHXEXEVKVHXEURZVHXEVIKKUSJZMJZVKVHYAXEVHVQWPWPYAXEOZWJWQWQVIKKUTZVAZUFZVHXTLVIMXTLOZVHVBUIZVCZULZULZUMZULZULZVHVMXDVLIJZVLVHKXDVJVLIVHXDKXRUFYMUMVHYNYNVLVHXGXGGZXGVKNFZGZGYNYNOVHYOYQVHXGXGXKXKUOVHXGYPXKVHVILWJLUGFZVHVDUIZUJZUOUOKKKVKUPSVHXDKVLVKIXRVHYPVLVKOYTVKUKSUMULULVE $.
$}
