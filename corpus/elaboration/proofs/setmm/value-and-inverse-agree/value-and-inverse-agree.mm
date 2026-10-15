$( proofs/setmm/value-and-inverse-agree/value-and-inverse-agree, elaborated from proofs/setmm/value-and-inverse-agree.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/setmm/inverse-of-value/inverse-of-value.mm $]
$[ proofs/setmm/value-of-inverse/value-of-inverse.mm $]

${
  proofs.setmm.value-and-inverse-agree.value-and-inverse-agree $p |- ( ( ( ( ( ( A e. _V /\ B e. _V ) /\ ( C : A --> B /\ C : A -1-1-> B ) ) /\ ( C " A ) = B ) /\ D e. A ) /\ E e. B ) -> ( ( C ` D ) = E <-> ( `' C ` E ) = D ) ) $=
    ( cvv wcel wa wf wf1 cima wceq cfv ccnv simpl id syl simpr jca proofs.setmm.inverse-of-value.inverse-of-value fveq2d eqeq1d mpbid proofs.setmm.value-of-inverse.value-of-inverse impbida ) AFGZBFGZHZABCIZABCJZHZHZCAKZBLZHZDAGZHZEBGZHZDCMZELZECNZMZDLZUSVAHZUTVBMZDLZVDVEUQVGVEUOUPVEULUNVEUHUKVEUFUGVEUSUFUSVAOZUSUQUFUQUROZUQUOUFUOUPOZUOULUFULUNOZULUHUFUHUKOZUHUFUFUFUGOZUFPZQZQZQZQZQZQVEUSUGVHUSUQUGVIUQUOUGVJUOULUGVKULUHUGVLUFUGRZQZQZQZQZQSVEUSUKVHUSUQUKVIUQUOUKVJUOULUKVKUHUKRZQZQZQZQSVEUSUNVHUSUQUNVIUQUOUNVJULUNRZQZQZQSVEUSUPVHUSUQUPVIUOUPRQQSABCDTQVEVFVCDVEUTEVBUSVARUAUBUCUSVDHZVCCMZELZVAWLUOURHWNWLUOURWLULUNWLUHUKWLUFUGWLUSUFUSVDOZVSQWLUSUGWOWDQSWLUSUKWOWHQSWLUSUNWOWKQSWLUSURWOUQURRQSABCEUDQWLWMUTEWLVCDCUSVDRUAUBUCUE $.
$}
