$( tests/elaborator/an-identity-a-link-drops/an-identity-a-link-drops, elaborated from tests/elaborator/an-identity-a-link-drops.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.an-identity-a-link-drops.an-identity-a-link-drops $p |- ( ( ( A : ZZ --> RR /\ B e. ZZ ) /\ ( ( A ` B ) x. ( 1 ^ B ) ) = ( ( A ` B ) x. 1 ) ) -> ( ( A ` B ) x. ( 1 ^ B ) ) = ( A ` B ) ) $=
    ( cz cr wf wcel wa cfv c1 cexp co cmul wceq simpr cc simpl id syl ffvelcdm syl2anc recn mulrid eqeq2d mpbid ) CDAEZBCFZGZBAHZIBJKZLKZUHILKZMZGZULUJUHMUGULNUMUKUHUJUMUHOFZUKUHMUMUHDFZUNUMUEUFUOUMUGUEUGULPZUGUEUEUEUFPUEQRRUMUGUFUPUEUFNRCDBASTUHUARUHUBRUCUD $.
$}
