$( proofs/setmm/member-of-image/member-of-image, elaborated from proofs/setmm/member-of-image.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d k m x $.
  $d A k m x $.
  $d B k m x $.
  $d C k m x $.
  $d D k m x $.
  $d E k m x $.
  proofs.setmm.member-of-image.member-of-image $p |- ( ( ( ( ( A e. _V /\ B e. _V ) /\ C : A --> B ) /\ D e. ~P A ) /\ E e. _V ) -> ( E e. ( C " D ) <-> E. x e. D ( C ` x ) = E ) ) $=
    ( cvv wcel wa wf cpw cima cv cfv wceq wrex vm simpr wss wb simpl syl elpwi jca gfvelima mpbid eqcomd id fveq2d eqeq1d rspcev ex rexlimdva mpd vk cbvrexvw a1i w3a 3jca gfnfvima eleq1d impbida ) BGHZCGHZIZBCDJZIZEBKZHZIZFGHZIZFDELZHZAMZDNZFOZAEPZVLVNIZFQMZDNZOZQEPZVRVSVNWCVLVNRVSVFEBSZIVNWCTVSVFWDVSVLVFVLVNUAZVLVJVFVJVKUAZVJVGVFVGVIUAZVEVFRZUBZUBZUBVSVIWDVSVLVIWEVLVJVIWFVGVIRZUBZUBEBUCZUBUDQBCFEDUEUBUFVSWBVRQEVSVTEHZIZWBVRWOWBIZWNWAFOZIVRWPWNWQWPWOWNWOWBUAVSWNRUBWPFWAWOWBRUGUDVQWQAVTEVOVTOZVPWAFWRVOVTDWRUHUIUJUKUBULUMUNVLVRIZUOMZDNZFOZUOEPZVNWSVRXCVLVRRVRXCTWSVQXBAUOEVOWTOZVPXAFXDVOWTDXDUHUIUJUPUQUFWSXBVNUOEWSWTEHZIZXBVNXFXBIZXAVMHZVNXGVFWDXEURXHXGVFWDXEXGXFVFXFXBUAZXFWSVFWSXEUAZWSVLVFVLVRUAZWJUBUBUBXGVIWDXGXFVIXIXFWSVIXJWSVLVIXKWLUBUBUBWMUBXGXFXEXIWSXERUBUSBCWTEDUTUBXGXAFVMXFXBRVAUFULUMUNVB $.
$}
