$( tests/elaborator/reading-memberships/a-membership-bound-in-a-requires-line, elaborated from tests/elaborator/reading-memberships.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.reading-memberships.a-membership-bound-in-a-requires-line $p |- ( ( ( ( A e. RR /\ B e. RR ) /\ C e. NN0 ) /\ A <_ B ) -> ( A x. C ) <_ ( B x. C ) ) $=
    ( cr wcel wa cn0 cle wbr cc0 w3a cmul co simpl id syl simpr nn0re nn0ge0 jca 3jca lemul1a ) ADEZBDEZFZCGEZFZABHIZFZUCUDCDEZJCHIZFZKZUHFACLMBCLMHIUIUMUHUIUCUDULUIUGUCUGUHNZUGUEUCUEUFNZUEUCUCUCUDNUCOPPPUIUGUDUNUGUEUDUOUCUDQPPUIUJUKUIUFUJUIUGUFUNUEUFQZPZCRPUIUFUKUQCSPTUAUGUHQTABCUBP $.
$}
