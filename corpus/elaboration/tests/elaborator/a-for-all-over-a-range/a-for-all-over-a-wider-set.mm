$( tests/elaborator/a-for-all-over-a-range/a-for-all-over-a-wider-set, elaborated from tests/elaborator/a-for-all-over-a-range.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d i j m $.
  $d A i j m $.
  tests.elaborator.a-for-all-over-a-range.a-for-all-over-a-wider-set $p |- ( ( A e. NN /\ A. i e. NN ( i / ( ! ` ( i + 1 ) ) ) e. RR ) -> sum_ j e. ( 1 ... ( A + 1 ) ) ( j / ( ! ` ( j + 1 ) ) ) = ( sum_ j e. ( 1 ... A ) ( j / ( ! ` ( j + 1 ) ) ) + ( ( A + 1 ) / ( ! ` ( ( A + 1 ) + 1 ) ) ) ) ) $=
    ( cn wcel cv c1 caddc co cfa cfv cdiv cr wral wa cuz simpl id syl elnnuz sylib cfz cc vm simpr wi elfznn wceq oveq1d fveq2d oveq12d eleq1d rspcv mpd ralrimiva cbvralvw recn fsump1 ) ADEZBFZUTGHIZJKZLIZMEZBDNZOZCFZVGGHIZJKZLIZAGHIZVKGHIZJKZLICGAVFUSAGPKEVFUSUSUSVEQUSRSATUAVFVGGVKUBIZEZOZVJMEZVJUCEVPVDBVNNZVQVPVFVRVFVOQVFUDFZVSGHIZJKZLIZMEZUDVNNVRVFWCUDVNVFVSVNEZOZVEWCWEVFVEVFWDQUSVEUESWEVSDEZVEWCUFWEWDWFVFWDUEVSVKUGSVDWCBVSDUTVSUHZVCWBMWGUTVSVBWALWGRZWGVAVTJWGUTVSGHWHUIUJUKULUMSUNUOWCVDUDBVNVSUTUHZWBVCMWIVSUTWAVBLWIRZWIVTVAJWIVSUTGHWJUIUJUKULUPUASVPVOVRVQUFVFVOUEVDVQBVGVNUTVGUHZVCVJMWKUTVGVBVILWKRZWKVAVHJWKUTVGGHWLUIUJUKULUMSUNVJUQSVGVKUHZVGVKVIVMLWMRZWMVHVLJWMVGVKGHWNUIUJUKUR $.
$}
