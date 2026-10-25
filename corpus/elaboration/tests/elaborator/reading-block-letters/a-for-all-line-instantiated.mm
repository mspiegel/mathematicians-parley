$( tests/elaborator/reading-block-letters/a-for-all-line-instantiated, elaborated from tests/elaborator/reading-block-letters.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d k m x y z $.
  tests.elaborator.reading-block-letters.a-for-all-line-instantiated $p |- ( A. x e. RR A. z e. RR ( x x. z ) = ( z x. x ) -> A. y e. RR ( y x. 2 ) = ( 2 x. y ) ) $=
    ( cv cmul co wceq cr wral vm c2 wcel wa simpl id syl wi simpr oveq1d oveq2d eqeq12d ralbidva rspcv mpd jca 2re a1i ralrimiva wb vk cbvralvw bitri mpbid ) ADZCDZEFZUOUNEFZGZCHIZAHIZJDZKEFZKVAEFZGZJHIZBDZKEFZKVFEFZGZBHIZUTVDJHUTVAHLZMZVAUOEFZUOVAEFZGZCHIZVDVLUTVPMVPVLUTVPVLUTUTUTVKNZUTOZPZVLUTVPVSVLVKUTVPQUTVKRUSVPAVAHUNVAGZURVOCHVTUOHLZMZUPVMUQVNWBUNVAUOEWBVTVTVTWANZVTOZPZSWBUNVAUOEWETUAUBUCPUDUEUTVPRPVLKHLZVPVDQWFVLUFUGVOVDCKHUOKGZVMVBVNVCWGUOKVAEWGOZTWGUOKVAEWHSUAUCPUDUHVEVJUIUTVEUJDZKEFZKWIEFZGZUJHIVJVDWLJUJHVAWIGZVBWJVCWKWMVAWIKEWMOZSWMVAWIKEWNTUAUKWLVIUJBHWIVFGZWJVGWKVHWOWIVFKEWOOZSWOWIVFKEWPTUAUKULUGUM $.
$}
