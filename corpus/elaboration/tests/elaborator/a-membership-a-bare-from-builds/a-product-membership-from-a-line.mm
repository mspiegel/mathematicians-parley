$( tests/elaborator/a-membership-a-bare-from-builds/a-product-membership-from-a-line, elaborated from tests/elaborator/a-membership-a-bare-from-builds.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.a-membership-a-bare-from-builds.a-product-membership-from-a-line $p |- ( ( ( ( ( ( ( A : NN --> NN /\ B e. NN ) /\ C e. ZZ ) /\ D e. ZZ ) /\ E e. ZZ ) /\ ( C x. ( A ` B ) ) || D ) /\ ( C x. ( A ` B ) ) || E ) -> ( C x. ( A ` B ) ) || ( D gcd E ) ) $=
    ( cn wf wcel wa cz cfv cmul co cdvds wbr cgcd simpl simpr syl jca w3a wi id ffvelcdm syl2anc nnz zmulcld 3jca dvdsgcd mpd ) FFAGZBFHZIZCJHZIZDJHZIZEJHZIZCBAKZLMZDNOZIZVAENOZIZVBVDIZVADEPMZNOZVEVBVDVEVCVBVCVDQZUSVBRSVCVDRTVEVAJHZUPURUAVFVHUBVEVJUPURVECUTVEVCUNVIVCUSUNUSVBQZUSUQUNUQURQZUQUOUNUOUPQZUMUNRSSSSVEUTFHZUTJHVEUKULVNVEVCUKVIVCUSUKVKUSUQUKVLUQUOUKVMUOUMUKUMUNQZUMUKUKUKULQUKUCSSSSSSVEVCULVIVCUSULVKUSUQULVLUQUOULVMUOUMULVOUKULRSSSSSFFBAUDUEUTUFSUGVEVCUPVIVCUSUPVKUSUQUPVLUOUPRSSSVEVCURVIVCUSURVKUQURRSSUHVADEUISUJ $.
$}
