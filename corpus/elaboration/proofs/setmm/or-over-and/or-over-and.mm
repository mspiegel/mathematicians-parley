$( proofs/setmm/or-over-and/or-over-and, elaborated from proofs/setmm/or-over-and.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  proofs.setmm.or-over-and.or-over-and $p |- ( ( ( A e. RR /\ B e. RR ) /\ C e. RR ) -> ( ( A = 0 \/ ( B = 0 /\ C = 0 ) ) <-> ( ( A = 0 \/ B = 0 ) /\ ( A = 0 \/ C = 0 ) ) ) ) $=
    ( cr wcel wa cc0 wceq wo simpr orc syl jca simpl olc mpjaodan simprd simpld impbida ) ADEZBDEZFZCDEZFZAGHZBGHZCGHZFZIZUEUFIZUEUGIZFZUDUIFZUEULUHUMUEFZUJUKUNUEUJUMUEJZUEUFKLUNUEUKUOUEUGKLMUMUHFZUJUKUPUFUJUPUHUFUMUHJZUFUGNLUFUEOLUPUGUKUPUHUGUQUFUGJLUGUEOLMUDUIJPUDULFZUEUIUFURUEFUEUIURUEJUEUHKZLURUFFZUEUIUGUTUEFUEUIUTUEJUSLUTUGFZUHUIVAUFUGVAUTUFUTUGNURUFJLUTUGJMUHUEOLUTURUKURUFNURUJUKUDULJZQLPURUJUKVBRPS $.
$}
