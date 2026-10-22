$( tests/stdlib/geometry/points-apart-by-coordinates, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.points-apart-by-coordinates $p |- ( ( ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. RR ) /\ D e. RR ) /\ E e. RR ) /\ F e. RR ) /\ A = ( C + ( _i x. D ) ) ) /\ B = ( E + ( _i x. F ) ) ) -> ( -. A = B <-> -. <. C , D >. = <. E , F >. ) ) $=
    ( cc wcel wa cr ci cmul co caddc wceq wne cop wb wn simpl simpr syl jca wi gptapart mpd df-ne a1i bibi12d mpbid ) AGHZBGHZIZCJHZIZDJHZIZEJHZIZFJHZIZACKDLMZNMZOZIZBEKFLMZNMZOZIZABPZCDQZEFQZPZRZABOZSZVKVLOZSZRVIVDVHIZVNVIVDVHVIVEVDVEVHTZVAVDUAUBVEVHUAUCVIUNUPIZURUTIZIVSVNUDVIWAWBVIUNUPVIVEUNVTVEVAUNVAVDTZVAUSUNUSUTTZUSUQUNUQURTZUQUOUNUOUPTUMUNUAUBUBUBUBUBVIVEUPVTVEVAUPWCVAUSUPWDUSUQUPWEUOUPUAUBUBUBUBUCVIURUTVIVEURVTVEVAURWCVAUSURWDUQURUAUBUBUBVIVEUTVTVEVAUTWCUSUTUAUBUBUCUCABCDEFUEUBUFVIVJVPVMVRVJVPRVIABUGUHVMVRRVIVKVLUGUHUIUJ $.
$}
