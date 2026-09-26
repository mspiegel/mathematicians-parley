$( proof/subsets/powerset-split-disjoint, elaborated from proof/subsets.proof by parley/elaborate.py.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d j k m $.
  $d A j k m $.
  $d B j k m $.
  powerse1 $p |- ( ( A e. _V /\ B e. A ) -> ( ~P ( A \ { B } ) i^i ran ( m e. ~P ( A \ { B } ) |-> ( m u. { B } ) ) ) = (/) ) $=
    ( cvv wcel wa vj cv csn cdif cpw wn cun cmpt crn wral cin c0 wceq vk simpl simpr elex syl snidg elun2 wss notnotr wb vex a1i snex jca unexg elpwg mpbid ssdifsn sylib simprd pm2.21dd ex pm2.18d ralrimiva id uneq1d eleq1d notbid cbvralvw eqid ralrnmpt mpbird disjr sylibr ) ADEZBAEZFZGHZABIZJZKZEZLZGCVTCHZVRMZNZOZPZVTWFQRSVPWGWDVTEZLZCVTPZVPTHZVRMZVTEZLZTVTPZWJVPWNTVTVPWKVTEZFZWNWQWNLZWNWQWRFZBWLEZWNWSWQWTWQWRUAWQBVREZWTWQBDEZXAWQVPXBVPWPUAVPVOXBVNVOUBBAUCUDUDBDUEUDBVRWKUFUDUDWSWLAUGZWTLZWSWLVSUGZXCXDFWSWMXEWSWRWMWQWRUBWMUHUDWSWLDEZWMXEUIWSWKDEZVRDEZFXFWSXGXHXGWSTUJUKXHWSBULZUKUMWKVRDDUNUDWLVSDUOUDUPWLABUQURUSUTVAVBVCWOWJUIVPWNWITCVTWKWCSZWMWHXJWLWDVTXJWKWCVRXJVDVEVFVGVHUKUPVPWDDEZCVTPWGWJUIVPXKCVTVPWCVTEZFZXLXHFXKXMXLXHVPXLUBXHXMXIUKUMWCVRVTDUNUDVCWBWICGVTWDWEDWEVIVQWDSZWAWHXNVQWDVTXNVDVFVGVJUDVKGVTWFVLVM $.
$}
