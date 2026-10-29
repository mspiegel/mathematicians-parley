$( tests/elaborator/a-naming-let-with-a-requires-line/a-naming-let-with-a-requires-line, elaborated from tests/elaborator/a-naming-let-with-a-requires-line.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d A m $.
  $d B m $.
  $d C m $.
  tests.elaborator.a-naming-let-with-a-requires-line.a-naming-let-with-a-requires-line $p |- ( ( ( ( ( ( A e. CC /\ B e. CC ) /\ C e. CC ) /\ -. A = B ) /\ -. C = B ) /\ -. A = C ) -> 0 <_ ( ( cos ` ( abs ` ( ( A - B ) ang ( C - B ) ) ) ) ^ 2 ) ) $=
    ( cc wcel wa wceq wn vm cv cmin co cang cabs cfv ccos wex cc0 c2 cexp cle wbr cvv fvex a1i elisset syl cr simpr simpl jca w3a wi id 3jca gangbnd3 mpd simpld recoscl eqeltrd sqge0 oveq1d breqtrd ex exlimdv ) ADEZBDEZFZCDEZFZABGZHZFZCBGZHZFZACGZHZFZIJZABKLZCBKLZMLZNOZPOZGZIQZRWESTLZUAUBZVSWEUCEZWGWJVSWDPUDUEIWEUCUFUGVSWFWIIVSWFWIVSWFFZRVTSTLZWHUAWKVTUHEZRWLUAUBWKVTWEUHVSWFUIZWKWDUHEZWEUHEZWKWORWDUAUBZWKVLVOFZWOWQFZWKVLVOWKVSVLVSWFUJZVSVPVLVPVRUJZVPVMVLVMVOUJZVJVLUIZUGZUGZUGZWKVSVOWTVSVPVOXAVMVOUIZUGZUGZUKZWKVFVGVIULZWRWSUMZWKVFVGVIWKVSVFWTVSVPVFXAVPVMVFXBVMVJVFVJVLUJZVJVHVFVHVIUJZVHVFVFVFVGUJZVFUNZUGZUGZUGZUGZUGZUGZWKVSVGWTVSVPVGXAVPVMVGXBVMVJVGXMVJVHVGXNVFVGUIZUGZUGZUGZUGZUGZWKVSVIWTVSVPVIXAVPVMVIXBVMVJVIXMVHVIUIZUGZUGZUGZUGZUOZABCUPZUGZUQZURZWDUSZUGZUTZVTVAUGWKVTWESTWKWFWMFWFWKWFWMWNUUAUKWFWMUJUGVBVCVDVEUQ $.
$}
