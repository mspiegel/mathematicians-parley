$( tests/elaborator/textbook-exercise-shapes/product-nonzero, elaborated from tests/elaborator/textbook-exercise-shapes.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.textbook-exercise-shapes.product-nonzero $p |- ( ( ( ( A e. RR /\ B e. RR ) /\ -. A = 0 ) /\ -. B = 0 ) -> -. ( A x. B ) = 0 ) $=
    ( cr wcel wa cc0 wceq wn cmul co cc simpl id syl recn 0cn a1i simpr wne neqcomd wb df-ne eqcom bicomd notbid bitrd mpbid c1 cexp eqidd exp1 eqcomd cn0 1nn0 expcld mullid eqtrd oveq12d ax-1cn mulcld mul02 eqtr4d mulcan2ad pm2.21dd ex pm2.01d ) ACDZBCDZEZAFGZHZEZBFGZHZEZABIJZFGZVOVQVQHZVOVQEZVJVRVSAFBVSVGAKDVSVOVGVOVQLZVOVLVGVLVNLZVLVIVGVIVKLZVIVGVGVGVHLVGMNNNNAONFKDVSPQVSVHBKDZVSVOVHVTVOVLVHWAVLVIVHWBVGVHRZNZNZNZBOZNZVSFBGZHZBFSZVSBFVSVOVNVTVLVNRNTVSWLWKVSWLVNWKWLVNUAVSBFUBQVSVMWJVSWJVMWJVMUAVSFBUCQUDUEUFUDUGVSVPFFBIJZVOVQRVSWMFVSWMFFVSWMFUHBUHUIJZIJZIJZFVSFFBWOIVSFUJZVSBWNWOVSWNBVSWCWNBGWIBUKNULVSWOWNVSWNKDWOWNGVSBUHWIUHUMDZVSUNQZUOZWNUPNULUQURVSWOKDWPFGVSUHWNUHKDVSUSQWTUTWOVANUQWQVBULUQVCVSVOVKVTVOVLVKWAVIVKRNNVDVEVF $.
$}
