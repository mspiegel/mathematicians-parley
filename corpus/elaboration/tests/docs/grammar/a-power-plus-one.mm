$( tests/docs/grammar/a-power-plus-one, elaborated from tests/docs/grammar.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d i j m $.
  $d A i j m $.
  $d B i j m $.
  tests.docs.grammar.a-power-plus-one $p |- ( ( A e. ZZ /\ B e. NN0 ) -> ( ( A ^ B ) + 1 ) e. ZZ ) $=
    ( cz wcel cn0 wa vj cv vm cn c1 caddc co cmul c2 cdiv cmpt wceq wex cexp cvv nnex a1i mptexg syl elisset vi cpr prex simpl id simpr zexpcld 1z jca zaddcl ex exlimdv mpd ) ACDZBEDZFZGHZIJIHZVDKLMZNMZOPMZQZRZGSZABTMZKLMZCDZVBVHUADZVJVBJUADZVNVOVBUBUCIJVGUAUDUEGVHUAUFUEVBVIVMGVBVIVMVBVIFZUGHZKOUHZRZUGSZVMVPVRUADZVTWAVPKOUIUCUGVRUAUFUEVPVSVMUGVPVSVMVPVSFZVKCDZKCDZFVMWBWCWDWBABWBVPUTVPVSUJZVPVBUTVBVIUJZVBUTUTUTVAUJUTUKUEUEUEWBVPVAWEVPVBVAWFUTVAULUEUEUMWDWBUNUCUOVKKUPUEUQURUSUQURUS $.
$}
