$( tests/elaborator/a-chain-showing-its-work/a-chain-line-citing-a-theorem, elaborated from tests/elaborator/a-chain-showing-its-work.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.a-chain-showing-its-work.a-chain-line-citing-a-theorem $p |- ( ( ( A e. RR /\ B e. RR ) /\ ( A x. 2 ) = ( B x. 2 ) ) -> A = ( B + 0 ) ) $=
    ( cr wcel wa c2 cmul co wceq cc0 caddc cc simpl id syl recn simpr 2cn a1i cn wne 2nn nnne0 mulcan2ad c1 cexp exp1 eqcomd cn0 1nn0 expcld mullid eqtrd eqidd oveq12d ax-1cn mulcld addrid eqtr4d ) ACDZBCDZEZAFGHZBFGHZIZEZABBJKHZVFABFVFUTALDVFVBUTVBVEMZVBUTUTUTVAMUTNOOAPOVFVABLDZVFVBVAVHUTVAQZOZBPZOZFLDVFRSVFFTDZFJUAVNVFUBSFUCOVBVEQUDVFBUEBUEUFHZGHZVGVFBVOVPVFVOBVFVIVOBIZVMBUGZOZUHZVFVPVOVFVOLDZVPVOIZVFBUEVMUEUIDZVFUJSZUKZVOULZOZUHZUMZVFVGVPJKHZVPVFBVPJJKWIVFJUNUOVFVPLDWJVPIVFUEVOUELDVFUPSWEUQVPUROUMUSUM $.
$}
