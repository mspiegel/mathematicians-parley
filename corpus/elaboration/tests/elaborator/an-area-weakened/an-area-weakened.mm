$( tests/elaborator/an-area-weakened/an-area-weakened, elaborated from tests/elaborator/an-area-weakened.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  tests.elaborator.an-area-weakened.an-area-weakened $p |- ( ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ -. A = C ) /\ -. B = C ) /\ 0 < ( ( ( 1 / 2 ) x. ( ( abs ` ( B - C ) ) x. ( abs ` ( A - C ) ) ) ) x. ( abs ` ( sin ` ( ( B - C ) ang ( A - C ) ) ) ) ) ) /\ ( ( ( ( 1 / 2 ) x. ( ( abs ` ( B - C ) ) x. ( abs ` ( A - C ) ) ) ) x. ( abs ` ( sin ` ( ( B - C ) ang ( A - C ) ) ) ) ) ^ 2 ) = ( 1 ^ 2 ) ) -> ( ( ( 1 / 2 ) x. ( ( abs ` ( B - C ) ) x. ( abs ` ( A - C ) ) ) ) x. ( abs ` ( sin ` ( ( B - C ) ang ( A - C ) ) ) ) ) = 1 ) $=
    ( cc wcel wa wceq wn cc0 c1 c2 cdiv co cmin cabs cfv cmul cang csin clt wbr cexp simpr cr cle wb wne simpl syl neqcomd df-ne a1i eqcom bicomd notbid bitrd mpbid jca w3a wi id 3jca gareacl mpd 0re ltled 1re 0lt1 ltle syl2anc sq11 ) ADEZBDEZFZCDEZFZACGZHZFZBCGZHZFZIJKLMZBCNMZOPZACNMZOPZQMZQMZWDWFRMZSPZOPZQMZTUAZFZWMKUBMZJKUBMZGZFZWRWMJGZWOWRUCWSWMUDEZIWMUEUAZFZJUDEZIJUEUAZFZFWRWTUFWSXCXFWSXAXBWSACUGZBCUGZFZXAWSXGXHWSCAGZHZXGWSACWSWOVRWOWRUHZWOWBVRWBWNUHZWBVSVRVSWAUHZVPVRUCZUIZUIZUIZUJZWSXGXKWSXGVRXKXGVRUFZWSACUKZULZWSVQXJWSXJVQXJVQUFZWSCAUMZULZUNZUOZUPZUNZUQZWSCBGZHZXHWSBCWSWOWAXLWOWBWAXMVSWAUCZUIZUIZUJZWSXHYLWSXHWAYLXHWAUFZWSBCUKZULZWSVTYKWSYKVTYKVTUFZWSCBUMZULZUNZUOZUPZUNZUQZURZWSVLVMVOUSZXIXAUTZWSVLVMVOWSWOVLXLWOWBVLXMWBVSVLXNVSVPVLVPVRUHZVPVNVLVNVOUHZVNVLVLVLVMUHZVLVAZUIZUIZUIZUIZUIZUIZWSWOVMXLWOWBVMXMWBVSVMXNVSVPVMUUKVPVNVMUULVLVMUCZUIZUIZUIZUIZUIZWSWOVOXLWOWBVOXMWBVSVOXNVSVPVOUUKVNVOUCZUIZUIZUIZUIZVBZABCVCZUIZVDZWSIWMIUDEZWSVEULZUVOWSWOWNXLWBWNUCUIVFURWSXDXEXDWSVGULZWSIJTUAZXEUVSWSVHULWSUVPXDUVSXEUTUVQUVRIJVIVJVDURURWMJVKUIUQ $.
$}
