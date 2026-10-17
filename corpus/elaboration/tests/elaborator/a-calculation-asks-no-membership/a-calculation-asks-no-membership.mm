$( tests/elaborator/a-calculation-asks-no-membership/a-calculation-asks-no-membership, elaborated from tests/elaborator/a-calculation-asks-no-membership.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.a-calculation-asks-no-membership.a-calculation-asks-no-membership $p |- ( ( ( ( A e. NN /\ B e. RR ) /\ B <_ ( 2 x. ( ! ` A ) ) ) /\ ( 2 x. ( ! ` A ) ) < ( ( 2 x. ( ! ` A ) ) x. 2 ) ) -> B < ( ( 2 x. ( ! ` A ) ) x. 2 ) ) $=
    ( cn wcel cr wa c2 cfa cfv cmul co cle wbr clt cxr simpl simpr syl lerelxr brel simpld simprd ltrelxr xrlelttrd ) ACDZBEDZFZBGAHIZJKZLMZFZUIUIGJKZNMZFZBUIULUNBODZUIODZUNUJUOUPFZUNUKUJUKUMPZUGUJQZRZBUIOOLSTZRZUAUNUOUPVBUBUNUPULODZUNUMUPVCFUKUMQZUIULOONUCTRUBUTVDUD $.
$}
