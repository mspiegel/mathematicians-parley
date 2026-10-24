$( tests/notations/for-all-functions/one-function-takes-its-value-in-its-codomain, elaborated from tests/notations/for-all-functions.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ tests/notations/for-all-functions/every-function-takes-its-values-in-its-codomain.mm $]

${
  $d A f $.
  $d B f $.
  $d C f $.
  $d D f $.
  tests.notations.for-all-functions.one-function-takes-its-value-in-its-codomain $p |- ( ( ( ( A e. _V /\ B e. _V ) /\ C e. A ) /\ D : A --> B ) -> ( D ` C ) e. B ) $=
    ( cvv wcel wa wf vf cv cfv cmap co wral simpl id syl simpr jca tests.notations.for-all-functions.every-function-takes-its-values-in-its-codomain wi wb elmapg mpbird wceq fveq1d eleq1d rspcv mpd ) AEFZBEFZGZCAFZGZABDHZGZCIJZKZBFZIBALMZNZCDKZBFZUPUNVAUPULUMUPUJUKUPUNUJUNUOOZUNULUJULUMOZULUJUJUJUKOZUJPZQZQZQZUPUNUKVDUNULUKVEUJUKRZQZQZSUPUNUMVDULUMRQSABCITQUPDUTFZVAVCUAUPVNUOUNUORUPUKUJGVNUOUBUPUKUJVMVJSBADEEUCQUDUSVCIDUTUQDUEZURVBBVOCUQDVOPUFUGUHQUI $.
$}
