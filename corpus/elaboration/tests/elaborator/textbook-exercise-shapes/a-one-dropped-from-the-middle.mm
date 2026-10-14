$( tests/elaborator/textbook-exercise-shapes/a-one-dropped-from-the-middle, elaborated from tests/elaborator/textbook-exercise-shapes.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.textbook-exercise-shapes.a-one-dropped-from-the-middle $p |- ( ( ( A e. NN0 /\ B e. ZZ ) /\ C e. NN0 ) -> ( ( ( A _C B ) x. ( 1 ^ C ) ) x. ( 1 ^ B ) ) = ( ( A _C B ) x. ( 1 ^ B ) ) ) $=
    ( cn0 wcel cz wa cbc co c1 cexp cmul wceq simpr nn0z syl 1exp oveq2d oveq1d cc simpl id jca bccl nn0cn mulrid eqtrd ) ADEZBFEZGZCDEZGZABHIZJCKIZLIZJBKIZLIUMJLIZUPLIUMUPLIULUOUQUPLULUNJUMLULCFEZUNJMULUKURUJUKNCOPCQPRSULUQUMUPLULUMTEZUQUMMULUMDEZUSULUJUTULUHUIULUJUHUJUKUAZUJUHUHUHUIUAUHUBPPULUJUIVAUHUINPUCBAUDPUMUEPUMUFPSUG $.
$}
