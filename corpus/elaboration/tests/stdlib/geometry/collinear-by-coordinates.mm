$( tests/stdlib/geometry/collinear-by-coordinates, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.collinear-by-coordinates $p |- ( ( ( ( ( ( ( A e. RR /\ B e. RR ) /\ C e. RR ) /\ D e. RR ) /\ E e. RR ) /\ F e. RR ) /\ -. <. A , B >. = <. C , D >. ) -> ( ( ( A + ( _i x. B ) ) = ( C + ( _i x. D ) ) \/ ( ( ( E + ( _i x. F ) ) - ( A + ( _i x. B ) ) ) / ( ( C + ( _i x. D ) ) - ( A + ( _i x. B ) ) ) ) e. RR ) <-> ( ( C - A ) x. ( F - B ) ) = ( ( E - A ) x. ( D - B ) ) ) ) $=
    ( cr wcel wa cop wceq wn wne ci cmul co caddc cmin cdiv wo wb simpr neqcomd df-ne a1i eqcom bicomd notbid bitrd mpbid wi simpl id syl jca gcolco mpd ) AGHZBGHZIZCGHZIZDGHZIZEGHZIZFGHZIZABJZCDJZKZLZIZVIVJMZANBOPZQPZCNDOPZQPZKZENFOPZQPZVPRPZVRVPRPZSPZGHZTZCARPZFBRPZOPZEARPZDBRPZOPZKZUAZVMVJVIKZLZVNVMVIVJVHVLUBUCVMVNWPVMVNVLWPVNVLUAVMVIVJUDUEVMVKWOVMWOVKWOVKUAVMVJVIUFUEUGUHUIUGUJVMUTVAVCIZIZVEVGIZIVNWNUKVMWRWSVMUTWQVMURUSVMVHURVHVLULZVHVFURVFVGULZVFVDURVDVEULZVDVBURVBVCULZVBUTURUTVAULZUTURURURUSULURUMUNUNUNUNUNUNVMVHUSWTVHVFUSXAVFVDUSXBVDVBUSXCVBUTUSXDURUSUBUNUNUNUNUNUOVMVAVCVMVHVAWTVHVFVAXAVFVDVAXBVDVBVAXCUTVAUBUNUNUNUNVMVHVCWTVHVFVCXAVFVDVCXBVBVCUBUNUNUNUOUOVMVEVGVMVHVEWTVHVFVEXAVDVEUBUNUNVMVHVGWTVFVGUBUNUOUOABCDEFUPUNUQ $.
$}
