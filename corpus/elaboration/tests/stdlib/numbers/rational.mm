$( tests/stdlib/numbers/rational, elaborated from tests/stdlib/numbers.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d k m p q x y $.
  $d A k m p q x y $.
  tests.stdlib.numbers.rational $p |- ( ( A e. RR /\ A e. QQ ) -> E. p e. ZZ E. q e. NN A = ( p / q ) ) $=
    ( cr wcel cq wa vx cv vy cdiv co wceq cn wrex cz simpr wb elq a1i mpbid vm vk id oveq2d eqeq2d cbvrexvw rexbii simpl syl oveq1d rexbidva bitri ) ADEZAFEZGZAHIZJIZKLZMZJNOZHPOZACIZBIZKLZMZBNOZCPOZUPUOVBUNUOQUOVBRUPHJASTUAVBVHRUPVBAUBIZUCIZKLZMZUCNOZUBPOZVHVBAUQVJKLZMZUCNOZHPOVNVAVQHPUTVPJUCNURVJMZUSVOAVRURVJUQKVRUDUEUFUGUHVQVMHUBPUQVIMZVPVLUCNVSVJNEZGZVOVKAWAUQVIVJKWAVSVSVSVTUIVSUDUJUKUFULUGUMVNAVIVDKLZMZBNOZUBPOVHVMWDUBPVLWCUCBNVJVDMZVKWBAWEVJVDVIKWEUDUEUFUGUHWDVGUBCPVIVCMZWCVFBNWFVDNEZGZWBVEAWHVIVCVDKWHWFWFWFWGUIWFUDUJUKUFULUGUMUMTUA $.
$}
