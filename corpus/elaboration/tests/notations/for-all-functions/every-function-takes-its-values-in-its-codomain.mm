$( tests/notations/for-all-functions/every-function-takes-its-values-in-its-codomain, elaborated from tests/notations/for-all-functions.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d f k m $.
  $d A f k m $.
  $d B f k m $.
  $d C f k m $.
  tests.notations.for-all-functions.every-function-takes-its-values-in-its-codomain $p |- ( ( ( A e. _V /\ B e. _V ) /\ C e. A ) -> A. f e. ( B ^m A ) ( f ` C ) e. B ) $=
    ( cvv wcel wa vm cv cfv cmap co wral wf simpr elmapi syl simpl jca ffvelcdm ralrimiva wb vk wceq id fveq1d eleq1d cbvralvw bitri a1i mpbid ) AEFZBEFZGZCAFZGZCHIZJZBFZHBAKLZMZCDIZJZBFZDUTMZUPUSHUTUPUQUTFZGZABUQNZUOGUSVGVHUOVGVFVHUPVFOUQBAPQVGUPUOUPVFRUNUOOQSABCUQTQUAVAVEUBUPVACUCIZJZBFZUCUTMVEUSVKHUCUTUQVIUDZURVJBVLCUQVIVLUEUFUGUHVKVDUCDUTVIVBUDZVJVCBVMCVIVBVMUEUFUGUHUIUJUK $.
$}
