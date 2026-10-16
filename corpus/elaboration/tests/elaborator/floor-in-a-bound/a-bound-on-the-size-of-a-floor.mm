$( tests/elaborator/floor-in-a-bound/a-bound-on-the-size-of-a-floor, elaborated from tests/elaborator/floor-in-a-bound.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  tests.elaborator.floor-in-a-bound.a-bound-on-the-size-of-a-floor $p |- ( ( ( A e. RR /\ ( abs ` ( |_ ` A ) ) = ( |_ ` A ) ) /\ ( |_ ` A ) <_ 1 ) -> ( abs ` ( |_ ` A ) ) <_ 1 ) $=
    ( cr wcel cfl cfv cabs wceq wa c1 cle wbr simpl simpr syl eqbrtrd ) ABCZADEZFEZQGZHZQIJKZHZRQIJUBTSTUALPSMNTUAMO $.
$}
