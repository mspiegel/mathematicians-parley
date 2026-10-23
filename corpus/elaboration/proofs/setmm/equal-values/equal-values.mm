$( proofs/setmm/equal-values/equal-values, elaborated from proofs/setmm/equal-values.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d s t $.
  $d A s t $.
  $d B s t $.
  $d C s t $.
  $d D s t $.
  $d E s t $.
  proofs.setmm.equal-values.equal-values $p |- ( ( ( ( ( A e. _V /\ B e. _V ) /\ ( C : A --> B /\ C : A -1-1-> B ) ) /\ D e. A ) /\ E e. A ) -> ( ( C ` D ) = ( C ` E ) <-> D = E ) ) $=
    ( cvv wcel wa wf wf1 cfv wceq simpr vt cv wi wral vs simpl syl wb dff13 a1i mpbid id fveq2d eqeq1d imbi12d ralbidva rspcv mpd eqeq2d impbida ) AFGZBFGZHZABCIZABCJZHZHZDAGZHZEAGZHZDCKZECKZLZDELZVDVGHZVGVHVDVGMVIVENOZCKZLZDVJLZPZNAQZVGVHPZVIROZCKZVKLZVQVJLZPZNAQZRAQZVOVIVDWCVDVGSZVDUQWCHZWCVDURWEVDUSURVDVBUSVBVCSZVBUTUSUTVASUPUSMTTUQURMTURWEUAVDRNABCUBUCUDUQWCMTTVIVAWCVOPVIVDVAWDVDVBVAWFUTVAMTTWBVORDAVQDLZWAVNNAWGVJAGZHZVSVLVTVMWIVRVEVKWIVQDCWIWGWGWGWHSZWGUEZTZUFUGWIVQDVJWLUGUHUIUJTUKVIVCVOVPPVIVDVCWDVBVCMTVNVPNEAVJELZVLVGVMVHWMVKVFVEWMVJECWMUEZUFULWMVJEDWNULUHUJTUKUKVDVHHDECVDVHMUFUM $.
$}
