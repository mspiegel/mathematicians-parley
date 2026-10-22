$( tests/stdlib/geometry/between-by-coordinates, elaborated from tests/stdlib/geometry.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.stdlib.geometry.between-by-coordinates $p |- ( ( ( ( ( ( A e. RR /\ B e. RR ) /\ C e. RR ) /\ D e. RR ) /\ E e. RR ) /\ F e. RR ) -> ( ( ( A + ( _i x. B ) ) =/= ( C + ( _i x. D ) ) /\ ( ( ( E + ( _i x. F ) ) - ( C + ( _i x. D ) ) ) / ( ( A + ( _i x. B ) ) - ( C + ( _i x. D ) ) ) ) e. RR /\ ( ( ( E + ( _i x. F ) ) - ( C + ( _i x. D ) ) ) / ( ( A + ( _i x. B ) ) - ( C + ( _i x. D ) ) ) ) < 0 ) <-> ( ( ( A - C ) x. ( F - D ) ) = ( ( E - C ) x. ( B - D ) ) /\ ( ( ( A - C ) x. ( E - C ) ) + ( ( B - D ) x. ( F - D ) ) ) < 0 ) ) ) $=
    ( cr wcel wa ci cmul co caddc wne cmin cdiv cc0 clt wbr w3a wceq wb simpl id syl simpr jca gbetco ) AGHZBGHZIZCGHZIZDGHZIZEGHZIZFGHZIZUKULUNIZIZUPURIZIAJBKLZMLZCJDKLZMLZNEJFKLZMLZVFOLZVDVFOLZPLZGHVKQRSTACOLZFDOLZKLECOLZBDOLZKLUAVLVNKLVOVMKLMLQRSIUBUSVAVBUSUKUTUSUIUJUSUQUIUQURUCZUQUOUIUOUPUCZUOUMUIUMUNUCZUMUKUIUKULUCZUKUIUIUIUJUCUIUDUEUEUEUEUEUSUQUJVPUQUOUJVQUOUMUJVRUMUKUJVSUIUJUFUEUEUEUEUGUSULUNUSUQULVPUQUOULVQUOUMULVRUKULUFUEUEUEUSUQUNVPUQUOUNVQUMUNUFUEUEUGUGUSUPURUSUQUPVPUOUPUFUEUQURUFUGUGABCDEFUHUE $.
$}
