$( tests/stdlib/functions/preimage, elaborated from tests/stdlib/functions.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.functions.preimage $p |- ( ( ( ( ( ( A e. _V /\ B e. _V ) /\ C e. _V ) /\ D : A --> B ) /\ E e. A ) /\ ( D ` E ) e. C ) -> E e. ( `' D " C ) ) $=
    ( cvv wcel wa wf cfv ccnv cima simpl simpr syl jca wb gelpreima mpbird ) AFGZBFGZHZCFGZHZABDIZHZEAGZHZEDJZCGZHZEDKZCLZGZUGUJHZUKUGUJUKUHUGUHUJMZUFUGNOUHUJNPUKUEUNUOQUKUHUEUPUHUFUEUFUGMUDUENOOABECDROS $.
$}
