$( proofs/setmm/size-of-union/union-split, elaborated from proofs/setmm/size-of-union.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d k m $.
  $d A k m $.
  $d B k m $.
  proofs.setmm.size-of-union.union-split $p |- ( ( A e. _V /\ B e. _V ) -> ( A u. ( B \ A ) ) = ( A u. B ) ) $=
    ( cvv wcel wa cdif cun wss wceq vm cv wral simpr elun1 syl wn wb eldif a1i mpbid simpl elun2 wo elun mpjaodan ralrimiva dfss3 mpbird vk wi orel1 mpd jca exmid eqss sylibr ) ACDZBCDZEZABAFZGZABGZHZVBVAHZEVAVBIUSVCVDUSVCJKZVBDZJVALZUSVFJVAUSVEVADZEZVEADZVFVEUTDZVIVJEVJVFVIVJMVEABNOVIVKEZVEBDZVFVLVMVJPZEZVMVLVKVOVIVKMVKVOQVLVEBARSTVMVNUAOVEBAUBOVIVHVJVKUCZUSVHMVHVPQVIVEAUTUDSTUEUFVCVGQUSJVAVBUGSUHUSVDUIKZVADZUIVBLZUSVRUIVBUSVQVBDZEZVQADZVRWBPZWAWBEWBVRWAWBMVQAUTNOWAWCEZVQUTDZVRWDWEVQBDZWCEZWDWFWCWDWBWFUCZWFWDWAWHWAWCUAWAVTWHUSVTMVTWHQWAVQABUDSTOWDWCWHWFUJWAWCMZWBWFUKOULWIUMWEWGQWDVQBARSUHVQUTAUBOWBWCUCWAWBUNSUEUFVDVSQUSUIVBVAUGSUHUMVAVBUOUP $.
$}
