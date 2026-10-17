$( proofs/hammack/scaled-gcd-bound/gcd-positive, elaborated from proofs/hammack/scaled-gcd-bound.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  proofs.hammack.scaled-gcd-bound.gcd-positive $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ -. ( A = 0 /\ B = 0 ) ) -> ( A gcd B ) e. NN ) $=
    ( cz wcel wa cc0 wceq wn cgcd co cn0 wne cn simpl id syl simpr jca gcdcl cdvds wbr gcddvds simpld breq1d mpbid wb 0dvds simprd pm2.21dd ex pm2.01d neqcomd df-ne a1i eqcom bicomd notbid bitrd elnnne0 sylibr ) ACDZBCDZEZAFGZBFGZEZHZEZABIJZKDZVIFLZEVIMDVHVJVKVHVCVJVHVAVBVHVCVAVCVGNZVCVAVAVAVBNZVAOZPZPZVHVCVBVLVAVBQZPZRZABSPVHFVIGZHZVKVHVIFVHVIFGZVHWBWBHZVHWBEZVFWCWDVDVEWDFATUAZVDWDVIATUAZWEWDVHWFVHWBNZVHWFVIBTUAZVHVCWFWHEZVSABUBZPZUCPWDVIFATVHWBQZUDUEWDVAWEVDUFWDVHVAWGVPPAUGPUEWDFBTUAZVEWDWHWMWDVHWHWGVHWFWHWKUHPWDVIFBTWLUDUEWDVBWMVEUFWDVHVBWGVRPBUGPUERWDVHVGWGVCVGQPUIUJUKULVHVKWAVHVKWCWAVKWCUFVHVIFUMUNVHWBVTVHVTWBVTWBUFVHFVIUOUNUPUQURUPUERVIUSUT $.
$}
