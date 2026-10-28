$( tests/stdlib/geometry/ruler, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d f k m u $.
  $d A f k m u $.
  $d B f k m u $.
  tests.stdlib.geometry.ruler $p |- ( ( ( A e. CC /\ B e. CC ) /\ -. A = B ) -> E. f e. ( RR ^m { u e. CC | ( A = B \/ ( ( u - A ) / ( B - A ) ) e. RR ) } ) ( f : { u e. CC | ( A = B \/ ( ( u - A ) / ( B - A ) ) e. RR ) } -1-1-onto-> RR /\ A. m e. { u e. CC | ( A = B \/ ( ( u - A ) / ( B - A ) ) e. RR ) } A. k e. { u e. CC | ( A = B \/ ( ( u - A ) / ( B - A ) ) e. RR ) } ( abs ` ( m - k ) ) = ( abs ` ( ( f ` m ) - ( f ` k ) ) ) ) ) $=
    ( cc wcel wa wceq wn wne cv cmin co cdiv cr wo crab wf1o cabs cfv wral cmap wrex simpr neqcomd wb df-ne a1i eqcom bicomd notbid bitrd mpbid wi simpl syl id gruler mpd ) BGHZCGHZIZBCJZKZIZBCLZVEAMZBNOZCBNOZPOZQHZRZAGSZQDMZTZFMZEMZNOZUAUBZVRVPUBZVSVPUBZNOZUAUBZJZEVOUCZFVOUCZIZDQVOUDOZUEZVGCBJZKZVHVGBCVDVFUFUGVGVHWMVGVHVFWMVHVFUHVGBCUIUJVGVEWLVGWLVEWLVEUHVGCBUKUJULUMUNULUOVGVCVHWKUPZVGVDVCVDVFUQZVBVCUFURVGVBVCWNUPVGVDVBWOVDVBVBVBVCUQVBUSURURFEABCDUTURVAVA $.
$}
