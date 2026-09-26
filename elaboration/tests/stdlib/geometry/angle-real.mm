$( tests/stdlib/geometry/angle-real, elaborated from tests/stdlib/geometry.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  anglerea $p |- ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ -. A = B ) /\ -. C = B ) -> ( ( abs ` ( ( A - B ) ang ( C - B ) ) ) e. RR /\ 0 <_ ( abs ` ( ( A - B ) ang ( C - B ) ) ) ) ) $=
    ( cc wcel wa wceq wn cmin co cang cabs cfv cr cc0 cle wbr simpl simpr syl jca w3a wi id 3jca gangbnd3 mpd ) ADEZBDEZFZCDEZFZABGZHZFZCBGZHZFZUNUQFZABIJZCBIJZKJZLMZNEZOVCPQZFZURUNUQURUOUNUOUQRZULUNSTUOUQSUAURUHUIUKUBUSVFUCURUHUIUKURUOUHVGUOULUHULUNRZULUJUHUJUKRZUJUHUHUHUIRUHUDTTTTURUOUIVGUOULUIVHULUJUIVIUHUISTTTURUOUKVGUOULUKVHUJUKSTTUEABCUFTUG $.
$}
