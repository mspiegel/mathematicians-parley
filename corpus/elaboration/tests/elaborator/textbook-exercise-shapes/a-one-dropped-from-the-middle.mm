$( tests/elaborator/textbook-exercise-shapes/a-one-dropped-from-the-middle, elaborated from tests/elaborator/textbook-exercise-shapes.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.textbook-exercise-shapes.a-one-dropped-from-the-middle $p |- ( ( ( A : ZZ --> RR /\ B e. ZZ ) /\ C e. NN0 ) -> ( ( ( A ` B ) x. ( 1 ^ C ) ) x. ( 1 ^ B ) ) = ( ( A ` B ) x. ( 1 ^ B ) ) ) $=
    ( cz cr wf wcel wa cn0 cfv c1 cexp co cmul wceq simpr nn0z syl 1exp oveq2d oveq1d cc simpl id ffvelcdm syl2anc recn mulrid eqtrd ) DEAFZBDGZHZCIGZHZBAJZKCLMZNMZKBLMZNMUOKNMZURNMUOURNMUNUQUSURNUNUPKUONUNCDGZUPKOUNUMUTULUMPCQRCSRTUAUNUSUOURNUNUOUBGZUSUOOUNUOEGZVAUNUJUKVBUNULUJULUMUCZULUJUJUJUKUCUJUDRRUNULUKVCUJUKPRDEBAUEUFUOUGRUOUHRUAUI $.
$}
