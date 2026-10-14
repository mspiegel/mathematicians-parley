$( tests/elaborator/an-identity-a-substitution-makes/an-identity-a-substitution-makes-at-a-value, elaborated from tests/elaborator/an-identity-a-substitution-makes.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.an-identity-a-substitution-makes.an-identity-a-substitution-makes-at-a-value $p |- ( ( ( A : ZZ --> RR /\ B e. ZZ ) /\ ( 1 ^ B ) = 1 ) -> ( ( A ` 0 ) x. ( 1 ^ B ) ) = ( A ` 0 ) ) $=
    ( cz cr wf wcel wa c1 cexp co wceq cc0 cfv cmul simpr oveq2d cc simpl id syl 0z a1i ffvelcdm syl2anc recn mulrid eqtrd ) CDAEZBCFZGZHBIJZHKZGZLAMZUKNJUNHNJZUNUMUKHUNNUJULOPUMUNQFZUOUNKUMUNDFZUPUMUHLCFZUQUMUJUHUJULRUJUHUHUHUIRUHSTTURUMUAUBCDLAUCUDUNUETUNUFTUG $.
$}
