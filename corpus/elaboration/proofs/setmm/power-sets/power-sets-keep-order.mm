$( proofs/setmm/power-sets/power-sets-keep-order, elaborated from proofs/setmm/power-sets.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ proofs/setmm/power-sets/set-is-a-part-of-itself.mm $]

${
  proofs.setmm.power-sets.power-sets-keep-order $p |- ( ( A e. _V /\ B e. _V ) -> ( A C_ B <-> ~P A C_ ~P B ) ) $=
    ( cvv wcel wa wss cpw simpr sspw syl simpl id proofs.setmm.power-sets.set-is-a-part-of-itself jca ssel2 wb elpwg mpbid impbida ) ACDZBCDZEZABFZAGZBGZFZUBUCEUCUFUBUCHABIJUBUFEZAUEDZUCUGUFAUDDZEUHUGUFUIUBUFHUGTUIUGUBTUBUFKZUBTTTUAKZTLZJZJZAMJNUDUEAOJUGTUHUCPUNABCQJRS $.
$}
