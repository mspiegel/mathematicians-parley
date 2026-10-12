$( tests/docs/syntax/nothing-to-show, elaborated from tests/docs/syntax.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d k m x $.
  $d A k m x $.
  $d B k m x $.
  $d C k m x $.
  tests.docs.syntax.nothing-to-show $p |- ( ( ( A e. NN0 /\ B e. _V ) /\ C : NN0 --> B ) -> A. x e. B ( ( ( 0 <_ A /\ x = ( C ` 0 ) ) /\ -. x = ( C ` 0 ) ) -> x = ( C ` A ) ) ) $=
    ( cn0 wcel cvv wa wf cc0 cle wbr vm cv cfv wceq wn wi wral simpr simpld simprd pm2.21dd ex ralrimiva wb vk id eqeq1d anbi2d notbid anbi12d imbi12d cbvralvw bitri a1i mpbid ) BEFZCGFZHZECDIZHZJBKLZMNZJDOZPZHZVFQZHZVDBDOZPZRZMCSZVCANZVEPZHZVOQZHZVNVJPZRZACSZVBVLMCVBVDCFZHZVIVKWCVIHZVFVKWDVCVFWDVGVHWCVITZUAUBWDVGVHWEUBUCUDUEVMWAUFVBVMVCUGNZVEPZHZWGQZHZWFVJPZRZUGCSWAVLWLMUGCVDWFPZVIWJVKWKWMVGWHVHWIWMVFWGVCWMVDWFVEWMUHZUIZUJWMVFWGWOUKULWMVDWFVJWNUIUMUNWLVTUGACWFVNPZWJVRWKVSWPWHVPWIVQWPWGVOVCWPWFVNVEWPUHZUIZUJWPWGVOWRUKULWPWFVNVJWQUIUMUNUOUPUQ $.
$}
