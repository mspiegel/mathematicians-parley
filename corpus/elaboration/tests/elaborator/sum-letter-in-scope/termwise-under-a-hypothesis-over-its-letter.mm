$( tests/elaborator/sum-letter-in-scope/termwise-under-a-hypothesis-over-its-letter, elaborated from tests/elaborator/sum-letter-in-scope.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d i j k m $.
  $d A i j k m $.
  tests.elaborator.sum-letter-in-scope.termwise-under-a-hypothesis-over-its-letter $p |- ( ( A e. NN /\ 0 <_ sum_ k e. ( 1 ... A ) k ) -> sum_ k e. ( 1 ... A ) ( k + 0 ) = sum_ k e. ( 1 ... A ) k ) $=
    ( cn wcel cc0 c1 cfz co cv csu cle wbr wa vj caddc wceq vm wral simpl cexp cmul cc cr cz simpr elfzelz syl zre recn exp1 eqcomd cn0 1nn0 a1i expcld mullid eqtrd eqidd oveq12d ax-1cn mulcld addrid eqtr4d ralrimiva wi id oveq1d eqeq12d rspcv mpd sumeq2dv wb vi cbvsumv eqeq1i eqeq2i bitri mpbid ) ACDZEFAGHZBIZBJZKLZMZVTNIZEOHZNJZVTWENJZPZVTWAEOHZBJZWBPZWDVTWFWENWDWEVTDZMZQIZEOHZWOPZQVTRZWFWEPZWNWDWRWDWMSWDWQQVTWDWOVTDZMZWPFWOFTHZUAHZWOXAWPXCEOHZXCXAWOXCEEOXAWOXBXCXAXBWOXAWOUBDZXBWOPZXAWOUCDZXEXAWOUDDZXGXAWTXHWDWTUEZWOFAUFZUGZWOUHZUGZWOUIZUGZWOUJZUGZUKZXAXCXBXAXBUBDZXCXBPZXAWOFXOFULDZXAUMUNZUOZXBUPZUGZUKZUQZXAEURUSXAXCUBDXDXCPXAFXBFUBDXAUTUNYCVAXCVBUGUQYGVCVDUGWNWMWRWSVEWDWMUEWQWSQWEVTWOWEPZWPWFWOWEYHWOWEEOYHVFZVGYIVHVIUGVJVKWIWLVLWDWIVTVMIZEOHZVMJZVTYJVMJZPZWLWIYLWHPYNWGYLWHVTWFYKNVMWEYJPZWEYJEOYOVFZVGVNVOWHYMYLVTWEYJNVMYPVNVPVQYNWKYMPWLYLWKYMVTYKWJVMBYJWAPZYJWAEOYQVFZVGVNVOYMWBWKVTYJWAVMBYRVNVPVQVQUNVR $.
$}
