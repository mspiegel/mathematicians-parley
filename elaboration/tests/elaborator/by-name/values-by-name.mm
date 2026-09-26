$( tests/elaborator/by-name/values-by-name, elaborated from tests/elaborator/by-name.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d m x y $.
  $d A m x y $.
  $d B m x y $.
  valuesby $p |- ( ( ( ( A e. ZZ /\ B e. ZZ ) /\ B = ( A x. 2 ) ) /\ A. x e. ZZ A. y e. ZZ ( x + y ) e. ZZ ) -> ( A || B /\ ( A + 1 ) e. ZZ ) ) $=
    ( cz wcel wa c2 cmul co wceq cv caddc wral cdvds wbr c1 vm wrex 2z a1i simpl simpr syl eqcomd jca id oveq2d eqeq1d rspcev wb divides cc zcn mulcom rexbidva bitrd mpbird wi oveq1d eleq1d ralbidv rspcv mpd 1z ) CEFZDEFZGZDCHIJZKZGZALZBLZMJZEFZBENZAENZGZCDOPZCQMJZEFZVRVSCRLZIJZDKZRESZVRHEFZVIDKZGWEVRWFWGWFVRTUAVRDVIVRVKVJVKVQUBZVHVJUCUDUEUFWDWGRHEWBHKZWCVIDWIWBHCIWIUGUHUIUJUDVRVSWBCIJZDKZRESZWEVRVHVSWLUKVRVFVGVRVKVFWHVKVHVFVHVJUBZVHVFVFVFVGUBZVFUGZUDZUDZUDZVRVKVGWHVKVHVGWMVFVGUCUDUDUFRCDULUDVRWKWDREVRWBEFZGZWJWCDWTWBUMFZCUMFZGWJWCKWTXAXBWTWSXAVRWSUCWBUNUDWTVFXBWTVRVFVRWSUBWRUDCUNUDUFWBCUOUDUIUPUQURVRCVMMJZEFZBENZWAVRVQXEVKVQUCVRVFVQXEUSWRVPXEACEVLCKZVOXDBEXFVNXCEXFVLCVMMXFUGUTVAVBVCUDVDVRQEFZXEWAUSXGVRVEUAXDWABQEVMQKZXCVTEXHVMQCMXHUGUHVAVCUDVDUF $.
$}
