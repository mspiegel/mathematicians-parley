$( tests/elaborator/reading-defines/a-define-read-in-an-unfolded-definition, elaborated from tests/elaborator/reading-defines.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d k m $.
  $d A k m $.
  $d B k m $.
  tests.elaborator.reading-defines.a-define-read-in-an-unfolded-definition $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( A + 1 ) = ( 2 x. B ) ) -> 2 || ( A + 1 ) ) $=
    ( cz wcel wa c1 caddc co c2 cmul wceq vm cv wex cdvds wbr cvv ovex a1i elisset syl vk wrex simpl simpr eqcomd eqeq1d mpbid wb eqcom eqeq2d bitrd jca id oveq2d rspcev 2z 1z zaddcld divides cc 2cn zcn mulcom rexbidva mpbird ex exlimdv mpd ) ACDZBCDZEZAFGHZIBJHZKZEZLMZVMKZLNZIVMOPZVPVMQDZVSWAVPAFGRSLVMQTUAVPVRVTLVPVRVTVPVREZVTIUBMZJHZVMKZUBCUCZWBVKVNVMKZEWFWBVKWGWBVPVKVPVRUDZVPVLVKVLVOUDZVJVKUEUAUAWBVQVNKZWGWBVOWJWBVPVOWHVLVOUEUAWBVMVQVNWBVQVMVPVRUEZUFUGUHWBWJVNVQKZWGWJWLUIWBVQVNUJSWBVQVMVNWKUKULUHUMWEWGUBBCWCBKZWDVNVMWMWCBIJWMUNUOUGUPUAWBVTWCIJHZVMKZUBCUCZWFWBICDZVMCDZEVTWPUIWBWQWRWQWBUQSWBAFWBVPVJWHVPVLVJWIVLVJVJVJVKUDVJUNUAUAUAFCDWBURSUSUMUBIVMUTUAWBWOWEUBCWBWCCDZEZWNWDVMWTWDWNWTIVADZWCVADZEWDWNKWTXAXBXAWTVBSWTWSXBWBWSUEWCVCUAUMIWCVDUAUFUGVEULVFVGVHVI $.
$}
