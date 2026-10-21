$( tests/stdlib/sets/pair-parts-equal, elaborated from tests/stdlib/sets.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.stdlib.sets.pair-parts-equal $p |- ( ( ( ( ( A e. RR /\ B e. RR ) /\ C e. RR ) /\ D e. RR ) /\ <. A , B >. = <. C , D >. ) -> ( A = C /\ B = D ) ) $=
    ( cr wcel wa cop wceq simpr cvv wb simpl id syl elex jca opthg mpbid ) AEFZBEFZGZCEFZGZDEFZGZABHZCDHZIZGZUIACIZBDIZGZUFUIJUJAKFZBKFZGUIUMLUJUNUOUJTUNUJUFTUFUIMZUFUDTUDUEMZUDUBTUBUCMZUBTTTUAMTNOOOOAEPOUJUAUOUJUFUAUPUFUDUAUQUDUBUAURTUAJOOOBEPOQABCDKKROS $.
$}
