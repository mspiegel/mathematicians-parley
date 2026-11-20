$( proofs/setmm/remainder-more/whole-plus-small, elaborated from proofs/setmm/remainder-more.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/setmm/remainder-facts/remainder-shifts.mm $]
$[ proofs/setmm/remainder-facts/remainder-of-small.mm $]

${
  proofs.setmm.remainder-more.whole-plus-small $p |- ( ( ( A e. NN0 /\ B e. NN ) /\ A < B ) -> ( ( B + A ) mod B ) = A ) $=
    ( cn0 wcel cn wa clt wbr caddc co cmo c1 cexp cmul cc wceq simpl simpr syl nncn exp1 eqcomd 1nn0 a1i expcld mullid eqtrd id nn0cn oveq12d ax-1cn mulcld addcom syl2anc eqidd eqtr4d oveq1d cr cc0 cz nn0re nnre jca nngt0 1z proofs.setmm.remainder-facts.remainder-shifts mulrid oveq2d eqeq1d mpbid cle nn0ge0 proofs.setmm.remainder-facts.remainder-of-small ) ACDZBEDZFZABGHZFZBAIJZBKJZABKJZAVRVTABIJZBKJZWAVRVSWBBKVRVSLALMJZNJZLBLMJZNJZIJZWBVRVSWGWEIJZWHVRBWGAWEIVRBWFWGVRWFBVRBODZWFBPZVRVOWJVRVPVOVPVQQZVNVORZSZBTZSZBUAZSZUBZVRWGWFVRWFODZWGWFPZVRBLWPLCDZVRUCUDZUEZWFUFZSZUBZUGZVRAWDWEVRWDAVRAODZWDAPZVRVNXIVRVPVNWLVPVNVNVNVOQZVNUHZSZSZAUIZSZAUAZSZUBZVRWEWDVRWDODZWEWDPZVRALXPXCUEZWDUFZSZUBZUGZUJVRWGODWEODWIWHPVRLWFLODZVRUKUDZXDULVRLWDYHYBULWGWEUMUNUGVRWBWHWHVRAWEBWGIYFXHUJVRWHUOUGUPUQVRABLNJZIJZBKJZWAPZWCWAPVRAURDZBURDZFZUSBGHZFZLUTDZFYLVRYQYRVRYOYPVRYMYNVRVNYMXNAVAZSZVRVOYNWNBVBZSZVCZVRVOYPWNBVDZSZVCZYRVRVEUDVCABLVFSVRYKWCWAVRYJWBBKVRYIBAIVRWJYIBPWPBVGSVHUQVIVJUGVRYQUSAVKHZFZVQFWAAPVRUUHVQVRYQUUGUUFVRVNUUGXNAVLSVCVPVQRVCABVMSUG $.
$}
